/-
SSZ Boolean primitive.

Mirrors `src/lean_spec/spec/ssz/boolean.py` in leanSpec:
  - `encode_bytes`: `True → 0x01`, `False → 0x00` (always 1 byte)
  - `decode_bytes`: accepts only a single byte that is 0x00 or 0x01;
                    anything else is a serialization error.

In Lean we model the error as `Option.none` (decode failure).

Proves SSZ-1 from `docs/lean4-proof-propositions.md`:
  `∀ b, Boolean.decode (Boolean.encode b) = some b`.
-/

namespace LeanSpec.SSZ

abbrev Boolean := Bool

namespace Boolean

def encode (b : Boolean) : ByteArray :=
  ByteArray.mk #[if b then 1 else 0]

def decode (bs : ByteArray) : Option Boolean :=
  match bs.data with
  | ⟨[0]⟩ => some false
  | ⟨[1]⟩ => some true
  | _     => none

theorem decode_encode (b : Boolean) :
    decode (encode b) = some b := by
  cases b <;> rfl

theorem encode_size (b : Boolean) : (encode b).size = 1 := by
  cases b <;> rfl

end Boolean
end LeanSpec.SSZ
