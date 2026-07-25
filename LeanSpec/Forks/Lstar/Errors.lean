/-
State-transition rejection errors.

Mirrors `src/lean_spec/spec/forks/lstar/errors.py` in leanSpec, where
`SpecRejectionError` carries a `RejectionReason`. The variants map to the
reasons raised by the modeled spec surface — the state-transition
function and fork-choice attestation validation:
  - `slotNotInFuture`                   ↔ `BLOCK_SLOT_NOT_IN_FUTURE`
  - `invalidSlot`                       ↔ `BLOCK_SLOT_MISMATCH`
  - `headerSlotNotNewer`                ↔ `BLOCK_OLDER_THAN_LATEST_HEADER`
  - `emptyValidatorRegistry`            ↔ `EMPTY_VALIDATOR_REGISTRY`
  - `proposerMismatch`                  ↔ `WRONG_PROPOSER`
  - `parentRootMismatch`                ↔ `PARENT_ROOT_MISMATCH`
  - `tooManyAttestationData`            ↔ `TOO_MANY_ATTESTATION_DATA`
  - `emptyAggregationBits`              ↔ `EMPTY_AGGREGATION_BITS`
  - `validatorIndexOutOfRange`          ↔ `VALIDATOR_INDEX_OUT_OF_RANGE`
  - `justifiedSlotOutOfRange`           ↔ `JUSTIFIED_SLOT_OUT_OF_RANGE`
  - `zeroHashJustificationRoot`         ↔ `ZERO_HASH_JUSTIFICATION_ROOT`
  - `justificationVotesLengthMismatch`  ↔ `JUSTIFICATION_VOTES_LENGTH_MISMATCH`
  - `unknownSourceBlock`                ↔ `UNKNOWN_SOURCE_BLOCK`
  - `unknownTargetBlock`                ↔ `UNKNOWN_TARGET_BLOCK`
  - `unknownHeadBlock`                  ↔ `UNKNOWN_HEAD_BLOCK`
  - `sourceAfterTarget`                 ↔ `SOURCE_AFTER_TARGET`
  - `headOlderThanTarget`               ↔ `HEAD_OLDER_THAN_TARGET`
  - `sourceSlotMismatch`                ↔ `SOURCE_SLOT_MISMATCH`
  - `targetSlotMismatch`                ↔ `TARGET_SLOT_MISMATCH`
  - `headSlotMismatch`                  ↔ `HEAD_SLOT_MISMATCH`
  - `sourceNotAncestorOfTarget`         ↔ `SOURCE_NOT_ANCESTOR_OF_TARGET`
  - `targetNotAncestorOfHead`           ↔ `TARGET_NOT_ANCESTOR_OF_HEAD`
  - `headNotDescendantOfFinalized`      ↔ `HEAD_NOT_DESCENDANT_OF_FINALIZED`
                                          (leanEthereum/leanSpec#1179)
  - `attestationSlotBeforeHead`         ↔ `ATTESTATION_SLOT_BEFORE_HEAD`
  - `attestationTooFarInFuture`         ↔ `ATTESTATION_TOO_FAR_IN_FUTURE`
  - `unknownParentBlock`                ↔ `UNKNOWN_PARENT_BLOCK`
  - `blockSlotGapTooLarge`              ↔ `BLOCK_SLOT_GAP_TOO_LARGE`
  - `blockTooFarInFuture`               ↔ `BLOCK_TOO_FAR_IN_FUTURE`
                                          (both added by
                                          leanEthereum/leanSpec#1182,
                                          fixing issue #1171)
  - `duplicateAttestationData`          ↔ `DUPLICATE_ATTESTATION_DATA`

The `STError` name is historical — the state-transition function was
modeled first; the type now carries every modeled rejection reason, like
upstream's single `RejectionReason` enum.

Python models failure by raising; Lean models it with `Except`, following
the catalog samples (`State.processBlockHeader s b = .ok s'`). Upstream
leanEthereum/leanSpec#1180 made the same separation type-level in Python:
`SpecRejectionError` now extends a dedicated `SpecError` base instead of
`AssertionError`, so protocol rejections and internal assertions are
distinguishable there too — matching what `Except STError` already
expresses here.

`parentRootMismatch` is pre-declared for the follow-up that widens the
`process_block_header` validation surface (it needs `hash_tree_root`).

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

import LeanSpec.Aliases

namespace LeanSpec.Forks.Lstar

/-- Reasons the state-transition function rejects a block. -/
inductive STError where
  | slotNotInFuture (current target : Slot) : STError
  | invalidSlot (expected actual : Slot) : STError
  | headerSlotNotNewer : STError
  | emptyValidatorRegistry : STError
  | parentRootMismatch (expected actual : Root) : STError
  | proposerMismatch (expected actual : ValidatorIndex) : STError
  | tooManyAttestationData (count max : Nat) : STError
  | emptyAggregationBits : STError
  | validatorIndexOutOfRange : STError
  | justifiedSlotOutOfRange (finalized target : Slot) : STError
  | zeroHashJustificationRoot : STError
  | justificationVotesLengthMismatch (expected actual : Nat) : STError
  | unknownSourceBlock (root : Root) : STError
  | unknownTargetBlock (root : Root) : STError
  | unknownHeadBlock (root : Root) : STError
  | sourceAfterTarget (source target : Slot) : STError
  | headOlderThanTarget (head target : Slot) : STError
  | sourceSlotMismatch (expected actual : Slot) : STError
  | targetSlotMismatch (expected actual : Slot) : STError
  | headSlotMismatch (expected actual : Slot) : STError
  | sourceNotAncestorOfTarget : STError
  | targetNotAncestorOfHead : STError
  | headNotDescendantOfFinalized : STError
  | attestationSlotBeforeHead (slot head : Slot) : STError
  | attestationTooFarInFuture (slot maxAdmissible : Nat) : STError
  | unknownParentBlock (root : Root) : STError
  | blockSlotGapTooLarge (slot parentSlot : Slot) : STError
  | blockTooFarInFuture (slot : Slot) (maxAdmissible : Nat) : STError
  | duplicateAttestationData : STError
  deriving Repr, BEq, Inhabited

/-- Result of a fallible state-transition step. -/
abbrev ST.Result := Except STError

end LeanSpec.Forks.Lstar
