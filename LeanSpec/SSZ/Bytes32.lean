/-
SSZ Bytes32 primitive.

Mirrors `src/lean_spec/spec/ssz/byte_arrays.py` in leanSpec:
  - `class Bytes32(BaseBytes)` with `LENGTH = 32` — a fixed-length 32-byte
    sequence (`BaseBytes` subclasses Python `bytes`)
  - Length is statically guaranteed: every value has `len(b) == 32`

In Lean we model this as a `ByteArray` subtype carrying the size invariant.

Proves SSZ-4 from `docs/lean4-proof-propositions.md`:
  `∀ bs : Bytes32, bs.size = 32`.
-/

namespace LeanSpec.SSZ

abbrev Bytes32 := { bs : ByteArray // bs.size = 32 }

namespace Bytes32

@[inline] def size (b : Bytes32) : Nat := b.val.size

theorem size_eq_32 (b : Bytes32) : b.size = 32 := b.property

/-- The all-zero 32-byte value (`Bytes32.zero()` in leanSpec, aka `ZERO_HASH`). -/
def zero : Bytes32 := ⟨⟨Array.replicate 32 0⟩, by simp [ByteArray.size]⟩

instance : Inhabited Bytes32 := ⟨zero⟩

instance : BEq Bytes32 := ⟨fun a b => a.val.data == b.val.data⟩

/-- `==` on `Bytes32` agrees with propositional equality (needed wherever
`Bytes32` keys an association-list map, e.g. the fork-choice store). -/
instance : LawfulBEq Bytes32 where
  eq_of_beq {a b} h := by
    have hd : a.val.data = b.val.data := eq_of_beq h
    have hv : a.val = b.val := by
      obtain ⟨⟨ad⟩, ha⟩ := a
      obtain ⟨⟨bd⟩, hb⟩ := b
      cases hd
      rfl
    exact Subtype.ext hv
  rfl {a} := by
    show (a.val.data == a.val.data) = true
    exact beq_self_eq_true _

instance : Repr Bytes32 := ⟨fun b n => reprPrec b.val.data n⟩

end Bytes32
end LeanSpec.SSZ
