/-
SSZ fixed-length Vector primitive.

Mirrors `src/lean_spec/spec/ssz/collections.py` in leanSpec:
  - `SSZVector[T]` with `LENGTH = n` is a fixed-length homogeneous sequence
    of exactly `n` elements (the fixed-length counterpart of the
    variable-length `SSZList`, which is bounded by `LIMIT` instead).
  - Length is statically guaranteed: every value has `len(v) == n`.

In Lean we model this as an `Array T` carrying the size invariant in the type,
exactly as `Bytes32` does for the 32-byte case. The invariant lives in the
structure rather than as an external precondition, so the length lemma is purely
structural.

Proves SSZ-5 from `docs/lean4-proof-propositions.md`:
  `∀ {T n} (v : SSZVector T n), v.data.size = n`.

Note: Lean's `Array` exposes `.size` (not `.length`); the two coincide for
`Array T`. The catalog statement is reconciled to `.size` accordingly.
-/

namespace LeanSpec.SSZ

/-- A fixed-length SSZ vector of `n` elements of type `T`. The length invariant
`data.size = n` is carried by the structure. -/
structure SSZVector (T : Type) (n : Nat) where
  data : Array T
  size_eq : data.size = n

namespace SSZVector

instance {T : Type} {n : Nat} [Inhabited T] : Inhabited (SSZVector T n) :=
  ⟨⟨Array.replicate n default, by simp⟩⟩

@[inline] def size {T : Type} {n : Nat} (v : SSZVector T n) : Nat := v.data.size

/-- SSZ-5: a fixed-length vector always holds exactly `n` elements. -/
theorem sszvector_length {T : Type} {n : Nat} (v : SSZVector T n) :
    v.data.size = n := v.size_eq

end SSZVector
end LeanSpec.SSZ
