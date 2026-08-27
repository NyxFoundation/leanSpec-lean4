/-
Block-store chain structure: every stored block's parent is stored, and
block acceptance is horizon-bounded.

The catalog sources STOR-1 to a `Database.add_block` parent-existence
precondition; in current leanSpec no such database method exists — the
gate lives in fork choice: `on_block`
(`src/lean_spec/spec/forks/lstar/fork_choice.py`) looks up the parent
*state* and rejects `UNKNOWN_PARENT_BLOCK` when it is absent, before
`SyncService._persist_block` writes anything, so a block reaches the
block map only when its parent is already there. The exception is the
chain anchor: `create_store` seeds the map with a block whose parent is
outside the tree — the zero hash for a genesis anchor, an absent block
for a checkpoint-sync anchor.

This file also mirrors leanEthereum/leanSpec#1182 (merged as `4ca7d27e`,
fixing issue #1171): right after the parent lookup, `on_block` bounds
the block's slot before the empty-slot loop of the state transition
runs — the slot may run at most `HISTORICAL_ROOTS_LIMIT` beyond the
parent state (`BLOCK_SLOT_GAP_TOO_LARGE`), and at most one slot past
the store clock (`BLOCK_TOO_FAR_IN_FUTURE`). Both guards are mirrored
from the merged diff.

Modeled as the guarded insertion `insertBlock` (the `on_block` gate
sequence at the point a block enters the block map, with the upstream
`dict` replace-by-key) on the fork-choice `Store`, and the invariant
`ParentsPresent` it maintains. The gate reads the *states* map exactly
as upstream does; carrying its presence over to the *blocks* map is the
blocks-states alignment invariant (`Store.WellFormed.blocksStatesAligned`,
issue #1176 M-4), which enters the preservation theorem as a
hypothesis.

Proves STOR-1 from `docs/lean4-proof-propositions.md` (and the horizon
bounds of issue #1171):
  - STOR-1: every non-anchor block has its parent in the store —
    anchoring establishes the invariant (`parentsPresent_anchor`),
    guarded insertion preserves it (`parentsPresent_insertBlock`), and
    on a genesis-anchored store it takes the catalog's form
    (`parent_exists_or_genesis`).
  - An accepted block sits at most `HISTORICAL_ROOTS_LIMIT` beyond its
    parent state (`insertBlock_slot_gap_bounded`) and at most one slot
    past the store clock (`insertBlock_within_horizon`) — the formal
    content of the #1182 fix.
-/

import LeanSpec.Forks.Lstar.Store.Ancestry

namespace LeanSpec.Storage

open LeanSpec.Forks.Lstar
open LeanSpec.Forks.Lstar.Store (getBlock?_eq_some_of_mem)

namespace Store

open LeanSpec.Forks.Lstar.Store

/-- Insert a block under its root, gated as `on_block` gates it at the
point where the block enters the store's block map: the parent *state*
must be known (`UNKNOWN_PARENT_BLOCK`), the slot may run at most
`HISTORICAL_ROOTS_LIMIT` beyond the parent (`BLOCK_SLOT_GAP_TOO_LARGE`
— the empty-slot loop in the transition runs once per slot from the
parent to the block), and at most one slot past the store clock
(`BLOCK_TOO_FAR_IN_FUTURE`), per leanEthereum/leanSpec#1182.
The insertion is the upstream `dict` assignment; it replaces any entry
with the same root, which upstream never exercises — `on_block`
early-returns on a block already in the store, so the write is always
fresh (`Store.onBlock` models that skip). Replace-by-key keeps this
model total without it. Python's negative slot gap and the truncated
`Nat` subtraction both pass the gap guard. -/
def insertBlock (st : LeanSpec.Forks.Lstar.Store) (root : Root)
    (b : Block) : ST.Result LeanSpec.Forks.Lstar.Store :=
  match st.getState? b.parentRoot with
  | none => .error (.unknownParentBlock b.parentRoot)
  | some parentState =>
    if HISTORICAL_ROOTS_LIMIT < b.slot.toNat - parentState.slot.toNat then
      .error (.blockSlotGapTooLarge b.slot parentState.slot)
    else if st.time.toNat / INTERVALS_PER_SLOT + 1 < b.slot.toNat then
      .error (.blockTooFarInFuture b.slot
        (st.time.toNat / INTERVALS_PER_SLOT + 1))
    else
      .ok { st with
        blocks := (root, b) :: st.blocks.filter (fun p => !(p.1 == root)) }

/-- STOR-1 invariant: every stored block is the chain anchor or has its
parent stored (the anchor's parent is outside the tree — the zero hash
for genesis, an absent block for a checkpoint-sync anchor). -/
def ParentsPresent (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root) : Prop :=
  ∀ p ∈ st.blocks,
    p.1 = anchorRoot ∨ (st.getBlock? p.2.parentRoot).isSome

/-- A freshly anchored store satisfies the invariant (`create_store`
seeds `blocks` with exactly the anchor). -/
theorem parentsPresent_anchor (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root) (anchorBlock : Block)
    (hblocks : st.blocks = [(anchorRoot, anchorBlock)]) :
    ParentsPresent st anchorRoot := by
  intro p hp
  rw [hblocks] at hp
  cases hp with
  | head => exact .inl rfl
  | tail _ h => cases h

/-- A successful lookup survives a replace-by-key insertion: the new
entry answers for its own root, and every other root still finds its
old entry behind the filter. -/
private theorem getBlock?_isSome_insert
    (st : LeanSpec.Forks.Lstar.Store) (root : Root) (b : Block) (k : Root)
    (h : (st.getBlock? k).isSome) :
    ((List.find? (fun p => p.1 == k)
      ((root, b) :: st.blocks.filter (fun p => !(p.1 == root)))).map
        (·.2)).isSome := by
  by_cases hk : (root == k) = true
  · simp [List.find?, hk]
  · rw [List.find?]
    simp only [hk]
    unfold LeanSpec.Forks.Lstar.Store.getBlock? at h
    have hroot : k ≠ root := fun hc => hk (hc ▸ beq_self_eq_true root)
    -- The old entry for `k` survives the filter, so `find?` still
    -- succeeds; induct over the block list.
    have : ∀ (l : List (Root × Block)),
        ((l.find? (fun p => p.1 == k)).map (·.2)).isSome →
        (((l.filter (fun p => !(p.1 == root))).find?
          (fun p => p.1 == k)).map (·.2)).isSome := by
      intro l
      induction l with
      | nil => intro hf; simp [List.find?] at hf
      | cons e t ih =>
        intro hf
        by_cases hek : (e.1 == k) = true
        · have hene : (e.1 == root) = false := by
            have : e.1 = k := eq_of_beq hek
            subst this
            exact beq_eq_false_iff_ne.mpr hroot
          rw [List.filter_cons_of_pos (by simp [hene])]
          simp [List.find?, hek]
        · rw [List.find?] at hf
          simp only [hek] at hf
          by_cases her : (e.1 == root) = true
          · rw [List.filter_cons_of_neg (by simp [her])]
            exact ih hf
          · rw [List.filter_cons_of_pos (by simp [her])]
            rw [List.find?]
            simp only [hek]
            exact ih hf
    exact this st.blocks h

/-- STOR-1, preservation: the parent-gated insertion keeps every stored
block's parent stored. The gate reads the states map, as upstream does;
the blocks-states alignment (`Store.WellFormed.blocksStatesAligned`,
issue #1176 M-4) carries the parent's presence over to the block map,
and a replace-by-key insertion never makes a present root absent. -/
theorem parentsPresent_insertBlock
    (st st' : LeanSpec.Forks.Lstar.Store) (anchorRoot root : Root)
    (b : Block)
    (halign : ∀ r : Root,
      (st.getBlock? r).isSome ↔ (st.getState? r).isSome)
    (hpp : ParentsPresent st anchorRoot)
    (h : insertBlock st root b = .ok st') :
    ParentsPresent st' anchorRoot := by
  unfold insertBlock at h
  split at h
  · simp at h
  · next parentState hparent =>
    split at h
    · simp at h
    · split at h
      · simp at h
      · injection h with h'
        subst h'
        intro p hp
        cases List.mem_cons.mp hp with
        | inl hnew =>
          subst hnew
          have hstate : (st.getState? b.parentRoot).isSome := by
            rw [hparent]; rfl
          exact .inr (getBlock?_isSome_insert st root b _
            ((halign b.parentRoot).mpr hstate))
        | inr hold =>
          have hmem := (List.mem_filter.mp hold).1
          cases hpp p hmem with
          | inl hanchor => exact .inl hanchor
          | inr hpresent =>
            exact .inr (getBlock?_isSome_insert st root b _ hpresent)

/-- STOR-1, catalog form: on a genesis-anchored store — the invariant
plus an anchor whose block carries the zero-hash parent — every stored
block's parent is the zero hash or itself stored. -/
theorem parent_exists_or_genesis (st : LeanSpec.Forks.Lstar.Store)
    (anchorRoot : Root)
    (hpp : ParentsPresent st anchorRoot)
    (hanchor : ∀ p ∈ st.blocks,
      p.1 = anchorRoot → p.2.parentRoot = SSZ.Bytes32.zero) :
    ∀ p ∈ st.blocks,
      p.2.parentRoot = SSZ.Bytes32.zero ∨
      (st.getBlock? p.2.parentRoot).isSome := by
  intro p hp
  cases hpp p hp with
  | inl hroot => exact .inl (hanchor p hp hroot)
  | inr hpresent => exact .inr hpresent

/-! ## Horizon bounds (issue #1171, fixed by leanEthereum/leanSpec#1182) -/

/-- An accepted block names a stored parent state and sits at most
`HISTORICAL_ROOTS_LIMIT` beyond it — the empty-slot loop the state
transition runs from the parent to the block is bounded. -/
theorem insertBlock_slot_gap_bounded
    (st st' : LeanSpec.Forks.Lstar.Store) (root : Root) (b : Block)
    (h : insertBlock st root b = .ok st') :
    ∃ parentState, st.getState? b.parentRoot = some parentState ∧
      b.slot.toNat - parentState.slot.toNat ≤ HISTORICAL_ROOTS_LIMIT := by
  unfold insertBlock at h
  split at h
  · simp at h
  · next parentState hparent =>
    split at h
    · simp at h
    · next hgap =>
      split at h
      · simp at h
      · exact ⟨parentState, hparent, Nat.le_of_not_lt hgap⟩

/-- An accepted block sits at most one slot past the store clock — the
future-slot horizon issue #1171 asked for. -/
theorem insertBlock_within_horizon
    (st st' : LeanSpec.Forks.Lstar.Store) (root : Root) (b : Block)
    (h : insertBlock st root b = .ok st') :
    b.slot.toNat ≤ st.time.toNat / INTERVALS_PER_SLOT + 1 := by
  unfold insertBlock at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · next hhorizon => exact Nat.le_of_not_lt hhorizon

end Store
end LeanSpec.Storage
