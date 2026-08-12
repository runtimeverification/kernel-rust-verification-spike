# Scoping: full Binder crate through Charon + Aeneas

Goal: see what blocks translating the whole `drivers/android/binder` crate (not
just the `allocation.rs` deserializer fragment already re-modelled), and rank
every distinct blocker for the Aeneas team. This is a scoping pass, not a proof.
No verification, no correctness claims.

Target: `drivers/android/binder` in Linux v7.2-rc2, 14 files, 8313 lines
(`process.rs` 1762, `thread.rs` 1661, `node.rs` 1139, `page_range.rs` 775,
`rust_binder_main.rs` 618, `allocation.rs` 611, plus 8 smaller files).

## Method

The crate cannot be compiled standalone (see blocker 0), so it cannot be handed
to Charon whole. Two sources of evidence instead:

- Per-construct probes: for each construct the crate uses, a minimal crate
  through `charon cargo --preset=aeneas` then `aeneas -backend lean`, recording
  the exact Aeneas outcome. Charon `909ff09a` / v0.1.220, Aeneas `c2015b86`.
- Static inventory: counts of each construct across all 14 files.

Each blocker below is tagged hard-stop (translation of the affected item fails),
opaque (translates, but the type/function is uninterpreted), or hack (a source
rewrite gets past it). "Cascade" means one failure aborts dependent declarations.

## Blocker 0: the crate does not compile without the kernel build environment

`cargo build` on `allocation.rs` alone gives 23 errors: unresolved `kernel`
crate, unresolved sibling modules (`crate::node`, `crate::process`, ...),
unresolved macros (`pr_warn!`). The crate is `#![no_std]` and routes everything
through the `kernel` crate and bindgen'd `bindings`. Charon runs as a rustc
driver, so it extracts nothing that rustc cannot compile.

This is an environment blocker, not an Aeneas limitation, and it comes first: to
translate the full crate at all, the build must supply the `kernel` crate and the
bindgen output, either by running Charon inside the kernel Rust build (Kbuild), or
by extending the hand-written stub layer from the deserializer spike to the whole
`kernel` surface the crate touches (34 distinct `kernel::` item paths, 43 distinct
`bindings::` symbols). The rest of this report concerns Aeneas translation
limitations, assuming that is solved.

## Aeneas translation blockers, ranked

Ranked by how much of the crate each blocks.

| Rank | Construct | Binder usage | Aeneas outcome (verbatim) | Class |
|---|---|---|---|---|
| 1 | Union type-punning | 4 unions; `BinderObject` is the deserializer core | `unions are not supported` then `Internal error`, cascades over every union-touching decl | hard-stop; hack: byte array (proven in `remodel/`) |
| 2 | Dynamic trait objects (`dyn`) | `dyn DeliverToRead`, the work-delivery core; 99 `ListArc`/`dyn` sites across `thread.rs`, `process.rs`, `node.rs`, `rust_binder_main.rs` | `Dynamic trait types are not supported yet`; the containing type and every dispatch site fail, cascades | hard-stop; no cheap hack |
| 3 | Function pointers / arrow types | arise from `dyn` vtables (0 hand-written `fn(...)` values) | `Function pointers are not supported yet`; `Arrow types are not supported yet` | hard-stop; subsumed by removing `dyn` |
| 4 | Pin-init (`#[pin_data]`, `PinInit`) | 10 pinned structs (`Process`, `Thread`, `Node`, `Context`, `Transaction`, ...) across 7 files | not reproducible standalone (needs the `kernel` init macros); unverified | unknown, flagged |

Everything else the crate uses translated in the probes.

## Translates, but only as opaque (semantics lost)

These are not translation blockers. Each extracts as an external, uninterpreted
definition (Aeneas prints "extracted external, unknown definitions"). The code
around them translates; their behaviour does not, so they are holes for any later
proof, not for translation.

| Construct | Binder usage | Probe result |
|---|---|---|
| `Arc` / `ARef` refcounting | 179 (`Arc` 171, `ARef` 8) | translates, opaque |
| `SpinLock` / `Mutex` | 30 | translates, opaque |
| Atomics / `Cell` / `RefCell` | 36 atomics, interior mutability | translates, opaque |
| `KVec` + `GFP_KERNEL` fallible alloc | 68 (`KVec` 18, `GFP_KERNEL` 50) | translates, opaque (fallible calls fit the `Result` monad) |
| C FFI (`extern "C"`, `bindings::`) | 43 distinct symbols, 70 call sites | translates, opaque |
| `Rc<RefCell<T>>` shared-mutable shape | closest analogue to `Arc<SpinLock<Inner>>` | translates, opaque |

## Translates cleanly (no issue in the probes)

Confirmed working, so not blockers: nested `&mut` through struct fields and
`mem::swap`; index-mutating `while` loops over slices (the `copy_transaction_data`
offset-loop shape); `FnMut` closures passed as `&mut F`; generic `FnOnce(&mut
[u8; N]) -> Result<()>` (the remodel needed a by-value rewrite for one specific
closure instantiation, but the general shape translates); trait associated types
with generic instantiation and `where` clauses; direct recursion; mutable global
`static` atomics; raw-pointer read/cast (Aeneas ships a `raw_pointers` test, and
the remodel's `MaybeUninit`/cast chain already translated). Aeneas's own test
suite also covers `dyn` in limited forms, closures, 9 loop shapes, traits, and
nested borrows, consistent with these results.

## Bottom line

Union support is not the only thing needed. Two hard-stops block full-crate
translation:

1. Union type-punning. Cascades from `BinderObject`. The byte-array rewrite is
   proven to get past it, at the cost of a fidelity argument.
2. Dynamic trait objects (`dyn DeliverToRead`), and the function pointers their
   vtables produce. This blocks the work-delivery path that `thread.rs`,
   `process.rs`, and `node.rs` are built around (99 sites). There is no
   byte-array-style rewrite; getting past it means replacing the trait object
   with a closed enum of the work variants, or monomorphizing, both of which
   change the source shape more than the union rewrite did.

A third item, pin-init (`#[pin_data]`), could not be exercised without the kernel
init macros and is unverified; it covers the 10 pinned structs that hold the core
binder state, so it needs a real test before the full-crate picture is complete.

Beyond translation: even with unions and `dyn` handled, the entire kernel
abstraction layer (`Arc`, locks, atomics, `KVec`, C FFI, 43 `bindings` symbols)
translates only as opaque. The full crate would produce Lean in which all kernel
behaviour is uninterpreted. That is enough for the Aeneas team's feature-planning
question, and it marks the boundary between "translates" and "can be reasoned
about".

## Reproduce

Per-construct probes live under a scratch directory, one crate each. For any
construct:

```sh
charon cargo --preset=aeneas                 # in the probe crate
aeneas -backend lean <name>.llbc -dest /tmp/out
```

Hard-stops print the messages quoted above; opaque cases print
"Generated: ..." plus the "extracted external, unknown definitions" warning.

Environment: Charon `909ff09a` (v0.1.220), Aeneas `c2015b86`, stable rustc 1.94.0.
