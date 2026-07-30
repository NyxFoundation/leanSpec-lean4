/-
Store pruning below the finalized root.

Models the memory-side optimization every production client ships but the
upstream reference spec (`src/lean_spec/spec/forks/lstar/`) is silent
about: the full block/state maps are kept forever, yet a node need only
retain the finalized subtree, because fork choice can never again
reference a block outside it (FC-2 `head_descends_from_justified`,
ST-4/ST-6 keeping the justified/finalized checkpoints ordered and the
finalized one irreversible).

This file delivers the memory-bound half of issue #71:
  - a **memory bound** — every retained block sits at or above the
    finalized slot, so the live store never exceeds the blocks from the
    finalized slot upward (`prune_blocks_length_le`,
    `prune_block_slot_ge`);
  - retained-set characterization — a block survives pruning iff the
    finalized checkpoint is its ancestor (`mem_prune_blocks_iff`);
  - pruning only drops entries (`prune_blocks_sublist`).

The observational-equivalence half (`update_head` / `on_block` /
checkpoint evolution agree between `st` and `prune st`, plus
`WellFormed` preservation) is follow-up work: the existing congruence
lemmas (`ancestorWalk_congr` etc.) require `blocks` equality, which
pruning deliberately breaks, so it needs a new prune-congruence family
("every root a finalized-subtree walk visits survives pruning").
-/

import LeanSpec.Forks.Lstar.Store.Ancestry

namespace LeanSpec.Forks.Lstar
namespace Store

/-- A block is retained by pruning iff the finalized checkpoint is an
ancestor of (or equal to) it — i.e. the block lies in the finalized
subtree. Decided by the same `checkpointIsAncestor` walk fork choice
already uses, on the checkpoint carrying the block's own slot. -/
def keepBlock (st : Store) (p : Root × Block) : Bool :=
  checkpointIsAncestor st st.latestFinalized ⟨p.1, p.2.slot⟩

/-- A state is retained iff its block is retained (keeping the
`blocks.keys = states.keys` alignment of `WellFormed`). -/
def keepState (st : Store) (p : Root × State) : Bool :=
  match st.getBlock? p.1 with
  | some b => keepBlock st (p.1, b)
  | none => false

/-- Drop every block/state outside the finalized subtree. The fork-choice
control fields (checkpoints, head, time, vote pools) are untouched — only
the block/state maps shrink, which is exactly what production clients do
once a checkpoint is final. -/
def prune (st : Store) : Store :=
  { st with
    blocks := st.blocks.filter (keepBlock st),
    states := st.states.filter (keepState st) }

@[simp] theorem prune_blocks (st : Store) :
    (prune st).blocks = st.blocks.filter (keepBlock st) := rfl

@[simp] theorem prune_states (st : Store) :
    (prune st).states = st.states.filter (keepState st) := rfl

/-- A block survives pruning iff the finalized checkpoint is its ancestor. -/
theorem mem_prune_blocks_iff {st : Store} {p : Root × Block} :
    p ∈ (prune st).blocks ↔
      p ∈ st.blocks ∧
      checkpointIsAncestor st st.latestFinalized ⟨p.1, p.2.slot⟩ = true := by
  simp [prune, List.mem_filter, keepBlock]

/-- Memory bound, per-block half: every retained block sits at or above
the finalized slot. `checkpointIsAncestor` returns `false` as soon as the
descendant slot dips below the ancestor slot, so nothing below the
finalized slot can survive. -/
theorem prune_block_slot_ge {st : Store} {p : Root × Block}
    (h : p ∈ (prune st).blocks) :
    st.latestFinalized.slot ≤ p.2.slot := by
  rw [mem_prune_blocks_iff] at h
  obtain ⟨_, hanc⟩ := h
  unfold checkpointIsAncestor at hanc
  by_cases hlt : p.2.slot < st.latestFinalized.slot
  · rw [if_pos hlt] at hanc; simp at hanc
  · exact UInt64.not_lt.mp hlt

/-- Filtering by a stronger predicate never yields a longer list. -/
private theorem filter_length_mono {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x → q x) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl 0
  | a :: t, h => by
    have ht : ∀ x ∈ t, p x → q x :=
      fun x hx hpx => h x (List.mem_cons_of_mem a hx) hpx
    rw [List.filter_cons, List.filter_cons]
    by_cases hpa : p a = true
    · have hqa : q a = true := h a List.mem_cons_self hpa
      rw [if_pos hpa, if_pos hqa, List.length_cons, List.length_cons]
      exact Nat.succ_le_succ (filter_length_mono p q t ht)
    · rw [if_neg hpa]
      by_cases hqa : q a = true
      · rw [if_pos hqa, List.length_cons]
        exact Nat.le_succ_of_le (filter_length_mono p q t ht)
      · rw [if_neg hqa]
        exact filter_length_mono p q t ht

/-- Memory bound: the live store after pruning is no larger than the set
of blocks sitting at or above the finalized slot. This is the statable
upper bound issue #71 feeds upstream — an unbounded store is replaced by
one bounded by the finalized-slot horizon. -/
theorem prune_blocks_length_le (st : Store) :
    (prune st).blocks.length ≤
      (st.blocks.filter
        (fun p => decide (st.latestFinalized.slot ≤ p.2.slot))).length := by
  rw [prune_blocks]
  refine filter_length_mono _ _ st.blocks (fun p hmem hkeep => ?_)
  have hge : st.latestFinalized.slot ≤ p.2.slot :=
    prune_block_slot_ge (by rw [mem_prune_blocks_iff]; exact ⟨hmem, hkeep⟩)
  simpa using hge

/-- Pruning only ever drops entries: the retained blocks are a sublist of
the originals (so also `(prune st).blocks.length ≤ st.blocks.length`). -/
theorem prune_blocks_sublist (st : Store) :
    (prune st).blocks.Sublist st.blocks := by
  rw [prune_blocks]; exact List.filter_sublist
