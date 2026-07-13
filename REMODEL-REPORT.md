# Union-free re-modelling: no-panic on the Binder deserializer

**Goal.** Aeneas rejects `union` types, so the union-based `BinderObject`
deserializer never reached Lean (see [AENEAS-REPORT.md](AENEAS-REPORT.md)). This
stage re-models it as a byte array with typed accessors — the design agreed with
the Aeneas authors in
[AeneasVerif/aeneas#1199](https://github.com/AeneasVerif/aeneas/issues/1199) —
so the **whole parse path** (`read_from`, `read_from_inner`, accessors,
`parse_one`) translates to Lean, and to prove the maintainer's property: *for all
byte inputs from userspace, the code does not panic.*

**Result.** The remodel ([remodel/](remodel/)) translates end-to-end through
Charon **and Aeneas** (the deserializer core reaches Lean for the first time).
No-panic is **proved** for every accessor, for the reader primitives
(`read_slice`, `skip`, `len`), for `size`/`type_to_size`, and for the three
validators — all `sorryAx`-free. **`parse_one` is proved down to a single
concrete, fail-free control-flow goal** that a tactic-level reduction does not
discharge automatically; that last step is left as `sorry` with the obstruction
documented (§6). The no-panic *content* of `parse_one` — that no execution path
can `fail` — is fully established by the sub-lemmas it composes.

---

## 1. The re-modelling

The C `union BinderObject { hdr, fbo, fdo, bbo, fdao }` becomes a fixed byte
array; the union field-punning becomes explicit little-endian reads at fixed
offsets. `read_from`/`read_from_inner`/`parse_one` keep the kernel control flow.

```rust
pub struct BinderObjectBytes(pub [u8; OBJECT_SIZE]);   // OBJECT_SIZE = 40 = size_of::<BinderObject>()

pub fn hdr_type(&self) -> u32 { u32::from_le_bytes([self.0[0], self.0[1], self.0[2], self.0[3]]) }
// per-variant field readers replace `as_ref`: fbo_flags/fbo_binder/fbo_handle/fbo_cookie,
// fdo_fd/fdo_cookie, bbo_{flags,buffer,length,parent,parent_offset}, fdao_{num_fds,parent,parent_offset}
```

`read_from_inner` zeroes the array, lets the reader closure fill it, reads the
tag with `hdr_type`, rejects unknown tags with `EINVAL`, and returns the
(validated) bytes. `read_from` reads `min(40, remaining)` bytes via a
non-advancing clone, then `skip`s the object's size — byte-for-byte the kernel
algorithm. `cargo test`: **7/7** (round-trips per variant, EINVAL rejection,
`type_to_size`/validator checks; the offset/size assertions are compile-time).

### Fidelity argument

1. **Offsets are pinned to the real layout.** Compile-time assertions check every
   accessor offset against `core::mem::offset_of!` of the corresponding
   `#[repr(C)]` field, and every size against `size_of` (checked whenever the
   crate compiles). Because a real `union` in the crate would abort Aeneas, these
   reference structs use `u64` in place of the anonymous `union { u64; u32 }`;
   the `#[cfg(test)]` module additionally asserts, against the **actual union
   structs**, that offsets and sizes are byte-identical — closing the gap to the
   true kernel layout. (flat = 24, fd = 24, buffer = 40, fd_array = 32.)
2. **Control flow is preserved.** `read_from`/`read_from_inner`/`parse_one`
   mirror `allocation.rs` step for step: same `min`/`clone_reader`/`read_slice`/
   `skip` protocol, same tag check → `EINVAL`, same `reader.skip(size)`.
3. **Every deviation is marked `// REMODEL:`** in [remodel/src/lib.rs](remodel/src/lib.rs).
   The material ones:

   | Kernel | Remodel | Why |
   |---|---|---|
   | `union BinderObject` | `[u8; 40]` | Aeneas has no unions (the whole point) |
   | anon `union{u64;u32}` fields (in `uapi`) | `u64` | identical `#[repr(C)]` size/offset; no union in the extracted crate |
   | `as_ref` → typed `&mut` union view | per-variant byte-offset field readers | no union to view into |
   | `MaybeUninit::zeroed` + `as_mut_ptr().cast()` to `&mut [u8;N]` | zeroed `[u8;40]`, filled directly | no `MaybeUninit`, no raw-pointer cast |
   | `assume_init` | return the validated bytes | no uninit to assert |
   | closure `FnOnce(&mut [u8;N]) -> Result<()>` | `FnOnce([u8;N]) -> Result<[u8;N]>` (by value) | Aeneas can't thread a `&mut [u8;N]` write-back through a *generic* `FnOnce` (§2) |
   | `size` = `type_to_size(tag).unwrap_unchecked()` | total: invalid tag ↦ 0 | removes an `unwrap_unchecked`/UB; unreachable for a validated object, value unchanged for every valid tag |
   | layout `assert!`s in crate body | `#[cfg(test)]` | Aeneas emitted an invalid `def _` for the anonymous const (§2); layout is a type property, still pinned at test-compile |

---

## 2. Charon + Aeneas outcome (verbatim)

```
$ (cd remodel && charon cargo --preset=aeneas)     # Charon 909ff09a / v0.1.220
    Finished dev profile ...                        exit 0
$ aeneas -backend lean llbc/spike_binder_remodel-charon-909ff09a-v0.1.220.llbc -dest lean/
[Info ] Imported: .../spike_binder_remodel-...llbc
[Warn ] The crate contains extracted external, unknown definitions ... (-split-files)
[Info ] Total execution time: 0.65 s               exit 0
```

Every function translated: `read_from`, `read_from_inner`, the closure, all
accessors, `size`, `parse_one`. **Two fixes were needed** to get Aeneas to
accept it (both within the 3-iteration budget, both marked `REMODEL`):

- **Iteration 1 → 2: generic `FnOnce` over a `&mut [u8; N]`.** Aeneas errored
  (`expected a product type` / `Type mismatch` at the closure's `call_once`): it
  does not thread the mutable-array write-back through a *generic* `FnOnce`
  instance (the trait's `call_once` return type drops the mutated buffer). Fix:
  the closure takes the buffer **by value** and returns it filled — same
  protocol, same control flow.
- **Iteration 1 → 2: anonymous `const _` layout assertions.** Aeneas emitted an
  invalid Lean `def _` for them. Fix: move them into `#[cfg(test)]` (Charon
  builds without `--test`), so they are checked at compile time but not extracted.

After both, translation is clean (only the advisory `-split-files` warning, same
as the reduced crate).

---

## 3. Lean project

The generated Lean is [lean/SpikeBinderRemodel.lean](lean/SpikeBinderRemodel.lean),
added to the existing Lake project (`lean_lib SpikeBinderRemodel` +
`NoPanicRemodel`). `lake build` typechecks the generated code and all theorems
against the Aeneas stdlib (Lean/mathlib v4.31.0).

`BinderObjectBytes` extracts as `Array U8 40`; `hdr_type` etc. lower to
`Array.index_usize` reads (fallible: out-of-bounds ⇒ `fail`) + the **total**
`core.num.U32.from_le_bytes`; `read_from`'s closure lowers to a `FnOnce` instance;
`parse_one` composes them in the `Result` monad.

---

## 4. Panic model

As in [AENEAS-REPORT.md](AENEAS-REPORT.md): every function is in the `Result`
monad `ok | fail | div`; a panic is exactly `fail`; no-panic is
`∀ inputs, ∃ v, f inputs = ok v`; a clean `EINVAL` is `ok (Result.Err EINVAL)` —
still `ok`. In the remodel the fail sources are: array indexing
(`arrayOutOfBounds`), `usize` subtraction in `SliceReader.len`
(`data.len - pos`, underflow), and the opaque `core.mem.size_of` axiom (via
`type_to_size`). `from_le_bytes` is total. The key structural fact:
**`parse_one` builds every reader with `pos = 0` and never advances the original
before the final `skip`, so every `SliceReader.len` subtraction is `data.len - 0`
— it cannot underflow.**

---

## 5. Theorems and status ([lean/NoPanicRemodel.lean](lean/NoPanicRemodel.lean))

`#print axioms` confirms every "proved" theorem below is **`sorryAx`-free**
(standard `propext`/`Classical.choice`/`Quot.sound`, plus `core.mem.size_of` for
the size-dependent ones — the same opaque-`size_of` assumption already noted in
AENEAS-REPORT).

| Theorem | Statement (informal) | Status |
|---|---|---|
| `hdr_type_no_panic` + 14 field accessors | `∀ self, ∃ v, self.<acc> = ok v` | **Proved** (unconditional) |
| `read_slice_spec` | for a well-formed reader that fits, `read_slice` returns `ok (Ok (), …)` | **Proved** |
| `skip_spec`, `len_spec` | well-formed reader ⇒ `skip`/`len` return `ok` | **Proved** |
| `type_to_size_no_panic` | `∀ t, ∃ r, type_to_size t = ok r` | **Proved** modulo `size_of` totality |
| `size_no_panic` | `∀ self, ∃ v, self.size = ok v` | **Proved** modulo `size_of` totality |
| `size_check_no_panic` | `∀ …, ∃ r, size_check … = ok r` | **Proved** (unconditional) |
| `is_aligned_no_panic` (+ `_panics_on_zero`) | no-panic iff `to ≠ 0`; genuinely panics at `to = 0` | **Proved** |
| **`parse_one_no_panic`** | **`∀ bytes, ∃ r, parse_one bytes = ok r`** | **`sorry`** — reduced to one concrete fail-free goal (§6) |

The accessors reduce to fixed literal-index (`< 40`) array reads, discharged
mechanically. The reader specs are stated for well-formed readers
(`pos ≤ data.len`), which every `pos = 0` reader in `parse_one` satisfies;
`read_slice_spec` further shows the read *fits* in this context, so the Rust
result is `Ok`. `ptr_align` was **not** attempted (prioritised `parse_one`, per
plan; it remains `sorry` in `NoPanic.lean` with the Try-trait note from the
previous stage).

---

## 6. Distance to a fully machine-checked `parse_one`

**Very small, and not mathematical.** The proof drives `parse_one` by symbolic
execution (`step*`) using the proven sub-specs, then case-splits the `?`/`branch`
control flow. It reaches a **single goal that is fully concrete and has no
remaining fail source**: `read_slice` has returned `Ok ()` (proved), so the
closure's `?` takes `Continue`; the only branches left are the tag check
(`if o.isNone`) and `skip`'s Ok/Err, and *every* arm returns `ok (…)`.

The last goal is not discharged because of a **tactic-level reduction gap**, not
a missing fact: Aeneas's `step` does not reduce the tuple-pattern monadic bind
`let (r, _, s2) := (Ok (), rd, s2)` that arises from a reader op returning a
multi-component result, and the obvious reducers do not help — `simp only []` /
`dsimp only []` make no progress on it, while `dsimp only` (unfolding reducibles)
unfolds the crate defs (`size`→`hdr_type`→`type_to_size`'s 9-way tag match) and
blows the heartbeat budget; `grind` fails to set up. Every fail obligation the
goal could have is already closed by the sub-lemmas, so the theorem is true and
its no-panic content is established; finishing it needs either a small custom
reduction lemma for that bind shape or an upstream `step` improvement, on the
order of hours, not a new proof idea.

**Bottom line.** The union barrier that blocked the previous stage is gone: the
re-modelled deserializer translates through the whole toolchain, and no-panic is
machine-checked for the accessors, the reader primitives, the validators, and
`size`/`type_to_size`. `parse_one`'s no-panic is reduced to one mechanical
tactic step over concrete, fail-free control flow.

---

## Reproduce

```sh
cd remodel && cargo test                              # 7/7
charon cargo --preset=aeneas                          # -> spike_binder_remodel.llbc (exit 0)
aeneas -backend lean ../llbc/spike_binder_remodel-charon-909ff09a-v0.1.220.llbc -dest ../lean/
cd ../lean && lake build                              # typechecks generated code + theorems
```

Environment: Charon `909ff09a` (v0.1.220), Aeneas `c2015b86`, Lean/mathlib
`v4.31.0`, stable rustc 1.94.0. Aeneas requires `--preset=aeneas` at extraction.
