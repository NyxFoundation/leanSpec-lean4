/-
Strictly-forward checkpoint replacement.

Mirrors `src/lean_spec/spec/forks/lstar/state_transition.py` in leanSpec:
  - `Checkpoint.advance_to` replaces a checkpoint only when the candidate's
    slot is strictly higher (`containers/checkpoint.py`; modeled inline as
    the strict comparison in `applyJustification`).
  - The finalization arm of `process_attestations` replaces
    `latest_finalized` only under the `finalized < source.slot` guard.

ST-3/ST-6 bound only the checkpoint *slots*: they admit a transition that
swaps a checkpoint to a different root at the same slot. This file closes
that gap: across a successful transition each of `latest_justified` /
`latest_finalized` is either unchanged as a whole value — root included —
or replaced by a checkpoint at a strictly higher slot. The one designed
exception is genesis anchoring (the first block fills in its parent root
at slot 0), excluded by the `latestBlockHeader.slot ≠ 0` hypothesis.

Cross-branch root *ancestry* is deliberately out of the STF's reach:
leanEthereum/leanSpec#1179 documents on `Checkpoint.advance_to` that
"selection is by slot only" and on `Store.latest_finalized` that the
ancestry is a separate store invariant.

Proves ST-7 from `docs/lean4-proof-propositions.md`:
  - ST-7: `State.transition s b = .ok s'` with a non-genesis latest header
    implies each checkpoint is unchanged or strictly slot-advanced
    (`checkpoint_forward`).
-/

import LeanSpec.Forks.Lstar.StateTransition

namespace LeanSpec.Forks.Lstar
namespace State

/-- "Unchanged or strictly forward" composes: stepping `a → b → c` where
each step keeps the checkpoint or strictly raises its slot yields the same
disjunction end to end. -/
private theorem forward_trans {a b c : Checkpoint}
    (h₁ : b = a ∨ a.slot < b.slot) (h₂ : c = b ∨ b.slot < c.slot) :
    c = a ∨ a.slot < c.slot := by
  cases h₁ with
  | inl hba =>
    cases h₂ with
    | inl hcb => exact .inl (hcb.trans hba)
    | inr hlt => exact .inr (by rw [← hba]; exact hlt)
  | inr hlt₁ =>
    cases h₂ with
    | inl hcb => exact .inr (by rw [hcb]; exact hlt₁)
    | inr hlt₂ =>
      exact .inr (UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_trans (UInt64.lt_iff_toNat_lt.mp hlt₁)
          (UInt64.lt_iff_toNat_lt.mp hlt₂)))

/-- `applyJustification` replaces each checkpoint only strictly forward:
the justified checkpoint moves only to a strictly later target, the
finalized checkpoint only to a source strictly past the old finalized
slot; otherwise both are returned unchanged, root included. -/
theorem applyJustification_forward (rootSlot : Root → Option Nat)
    (acc : JFAcc) (src tgt : Checkpoint) :
    ((applyJustification rootSlot acc src tgt).latestJustified
        = acc.latestJustified ∨
      acc.latestJustified.slot <
        (applyJustification rootSlot acc src tgt).latestJustified.slot) ∧
    ((applyJustification rootSlot acc src tgt).latestFinalized
        = acc.latestFinalized ∨
      acc.latestFinalized.slot <
        (applyJustification rootSlot acc src tgt).latestFinalized.slot) := by
  unfold applyJustification
  dsimp only
  split
  · next hfin =>
    refine ⟨?_, .inr hfin.1⟩
    split
    · next hlt => exact .inr hlt
    · exact .inl rfl
  · refine ⟨?_, .inl rfl⟩
    split
    · next hlt => exact .inr hlt
    · exact .inl rfl

/-- One attestation step keeps each checkpoint or strictly advances its
slot: the vote filters and a stored tally leave both untouched, and the
supermajority path is `applyJustification`. -/
theorem processAttestation_forward (validatorCount : Nat) (hist : Array Root)
    (rootSlot : Root → Option Nat) (acc acc' : JFAcc)
    (att : AggregatedAttestation)
    (h : processAttestation validatorCount hist rootSlot acc att = .ok acc') :
    (acc'.latestJustified = acc.latestJustified ∨
      acc.latestJustified.slot < acc'.latestJustified.slot) ∧
    (acc'.latestFinalized = acc.latestFinalized ∨
      acc.latestFinalized.slot < acc'.latestFinalized.slot) := by
  unfold processAttestation at h
  dsimp only at h
  split at h
  · simp at h
  · injection h with h'
    subst h'
    exact ⟨.inl rfl, .inl rfl⟩
  · split at h
    · simp at h
    · injection h with h'
      subst h'
      exact ⟨.inl rfl, .inl rfl⟩
    · split at h
      · injection h with h'
        subst h'
        exact ⟨.inl rfl, .inl rfl⟩
      · split at h
        · injection h with h'
          subst h'
          exact ⟨.inl rfl, .inl rfl⟩
        · split at h
          · injection h with h'
            subst h'
            exact ⟨.inl rfl, .inl rfl⟩
          · split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · injection h with h'
                  subst h'
                  exact ⟨.inl rfl, .inl rfl⟩
                · injection h with h'
                  subst h'
                  exact applyJustification_forward rootSlot acc
                    att.data.source att.data.target

/-- Folding attestation steps preserves strictly-forward replacement. -/
theorem foldlM_processAttestation_forward (validatorCount : Nat)
    (hist : Array Root) (rootSlot : Root → Option Nat) :
    ∀ (atts : List AggregatedAttestation) (acc acc' : JFAcc),
    List.foldlM (processAttestation validatorCount hist rootSlot) acc atts
      = .ok acc' →
    (acc'.latestJustified = acc.latestJustified ∨
      acc.latestJustified.slot < acc'.latestJustified.slot) ∧
    (acc'.latestFinalized = acc.latestFinalized ∨
      acc.latestFinalized.slot < acc'.latestFinalized.slot)
  | [], acc, acc', h => by
    injection h with h'
    subst h'
    exact ⟨.inl rfl, .inl rfl⟩
  | att :: atts, acc, acc', h => by
    rw [List.foldlM_cons] at h
    cases hstep : processAttestation validatorCount hist rootSlot acc att with
    | error e =>
      rw [hstep] at h
      injection h
    | ok acc₁ =>
      rw [hstep] at h
      have hrest :
          List.foldlM (processAttestation validatorCount hist rootSlot) acc₁
            atts = .ok acc' := h
      have h1 := processAttestation_forward validatorCount hist rootSlot acc
        acc₁ att hstep
      have h2 := foldlM_processAttestation_forward validatorCount hist
        rootSlot atts acc₁ acc' hrest
      exact ⟨forward_trans h1.1 h2.1, forward_trans h1.2 h2.2⟩

/-- `processAttestations` keeps each checkpoint or strictly advances its
slot — never a same-slot root swap. -/
theorem processAttestations_forward (s s' : State)
    (atts : List AggregatedAttestation)
    (h : processAttestations s atts = .ok s') :
    (s'.latestJustified = s.latestJustified ∨
      s.latestJustified.slot < s'.latestJustified.slot) ∧
    (s'.latestFinalized = s.latestFinalized ∨
      s.latestFinalized.slot < s'.latestFinalized.slot) := by
  unfold processAttestations at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · next acc heq =>
            injection h with h'
            subst h'
            exact foldlM_processAttestation_forward _ _ _ atts _ acc heq

/-- Past genesis anchoring, `processBlockHeader` leaves both checkpoints
untouched: the anchor branch fires only when the latest header still sits
at slot 0. -/
theorem processBlockHeader_checkpoints_of_ne_zero (s s' : State) (b : Block)
    (hnz : s.latestBlockHeader.slot ≠ 0)
    (h : processBlockHeader s b = .ok s') :
    s'.latestJustified = s.latestJustified ∧
    s'.latestFinalized = s.latestFinalized := by
  unfold processBlockHeader at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · injection h with h'
          subst h'
          exact ⟨rfl, rfl⟩

/-- ST-7: checkpoint replacement is strictly forward across a successful
transition on a post-anchoring state — each of `latestJustified` /
`latestFinalized` is unchanged as a whole checkpoint (root included) or
moves to a strictly higher slot. A same-slot root swap is impossible. -/
theorem checkpoint_forward (s s' : State) (b : Block)
    (hnz : s.latestBlockHeader.slot ≠ 0)
    (h : transition s b = .ok s') :
    (s'.latestJustified = s.latestJustified ∨
      s.latestJustified.slot < s'.latestJustified.slot) ∧
    (s'.latestFinalized = s.latestFinalized ∨
      s.latestFinalized.slot < s'.latestFinalized.slot) := by
  unfold transition at h
  split at h
  · simp at h
  · unfold processBlock at h
    split at h
    · simp at h
    · next s₁ hh =>
      have hps := processSlots_checkpoints s b.slot
      have hnz' : (processSlots s b.slot).latestBlockHeader.slot ≠ 0 := by
        rw [hps.2.2]; exact hnz
      have hhdr :=
        processBlockHeader_checkpoints_of_ne_zero _ _ b hnz' hh
      rw [hps.1] at hhdr
      rw [hps.2.1] at hhdr
      have hatt := processAttestations_forward _ _ _ h
      rw [hhdr.1, hhdr.2] at hatt
      exact hatt

end State
end LeanSpec.Forks.Lstar
