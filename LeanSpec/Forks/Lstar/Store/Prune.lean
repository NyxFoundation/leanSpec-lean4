/-
Store pruning below the finalized root.

Models the memory-side optimization every production client ships but the
upstream reference spec (`src/lean_spec/spec/forks/lstar/`) is silent
about: the full block/state maps are kept forever, yet a node need only
retain the finalized subtree, because fork choice can never again
reference a block outside it (FC-2 `head_descends_from_justified`,
ST-4/ST-6 keeping the justified/finalized checkpoints ordered and the
finalized one irreversible).

This file delivers the memory-bound and invariant halves of issue #71:
  - a **memory bound** — every retained block sits at or above the
    finalized slot, so the live store never exceeds the blocks from the
    finalized slot upward (`prune_blocks_length_le`,
    `prune_block_slot_ge`);
  - retained-set characterization — a block survives pruning iff the
    finalized checkpoint is its ancestor (`mem_prune_blocks_iff`,
    `getBlock?_prune_iff`, `getState?_prune_iff`);
  - pruning only drops entries (`prune_blocks_sublist`);
  - **pruning preserves `WellFormed`** (`prune_wellFormed`) — the
    justified anchor and its finalized ancestry survive because the
    justified root lies on the finalized subtree (M-1) and every node a
    finalized-subtree walk visits descends from the finalized block
    (`ancestorWalk_sound`, `keepBlock_of_ancestorOrEqual`,
    `properAncestor_prune`).

The observational-equivalence half (`update_head` / `on_block` agree
between `st` and `prune st`) is follow-up work; it builds on the
subtree-transfer lemmas proved here.
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

/-! ## Lookups on the pruned store -/

/-- On an association list with unique keys, looking a key up after
filtering finds the original entry exactly when the filter keeps it. -/
private theorem assocFind?_filter {α : Type} (q : Root × α → Bool)
    (r : Root) :
    ∀ (l : List (Root × α)), (l.map (·.1)).Nodup →
      (l.filter q).find? (fun p => p.1 == r)
        = match l.find? (fun p => p.1 == r) with
          | some e => if q e then some e else none
          | none => none
  | [], _ => rfl
  | e :: t, hnd => by
    have hnd' : (t.map (·.1)).Nodup ∧ e.1 ∉ t.map (·.1) := by
      rw [List.map_cons, List.nodup_cons] at hnd
      exact ⟨hnd.2, hnd.1⟩
    by_cases her : e.1 = r
    · rw [List.find?_cons_of_pos (by simp [her])]
      by_cases hq : q e = true
      · rw [List.filter_cons, if_pos hq,
          List.find?_cons_of_pos (by simp [her])]
        dsimp only
        rw [if_pos hq]
      · rw [List.filter_cons, if_neg hq]
        dsimp only
        rw [if_neg hq]
        -- The unique key-`r` entry was dropped: no other entry matches.
        rw [List.find?_eq_none]
        intro x hx
        have hxt : x ∈ t := (List.mem_filter.mp hx).1
        simp only [beq_iff_eq]
        intro hxr
        apply hnd'.2
        rw [her]
        exact List.mem_map.mpr ⟨x, hxt, hxr⟩
    · rw [List.find?_cons_of_neg (by simp [her])]
      by_cases hq : q e = true
      · rw [List.filter_cons, if_pos hq,
          List.find?_cons_of_neg (by simp [her])]
        exact assocFind?_filter q r t hnd'.1
      · rw [List.filter_cons, if_neg hq]
        exact assocFind?_filter q r t hnd'.1

/-- Block lookup on the pruned store: the original entry, exactly when
pruning keeps it. -/
theorem getBlock?_prune_iff {st : Store}
    (hnd : (st.blocks.map (·.1)).Nodup) (r : Root) (b : Block) :
    (prune st).getBlock? r = some b ↔
      st.getBlock? r = some b ∧ keepBlock st (r, b) = true := by
  unfold getBlock?
  rw [prune_blocks, assocFind?_filter (keepBlock st) r st.blocks hnd]
  cases hf : st.blocks.find? (fun p => p.1 == r) with
  | none => simp
  | some e =>
    obtain ⟨e1, e2⟩ := e
    have he1 : e1 = r := eq_of_beq
      (List.find?_some (p := fun (p : Root × Block) => p.1 == r) hf)
    subst he1
    by_cases hq : keepBlock st (e1, e2) = true
    · dsimp only
      rw [if_pos hq]
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hq⟩
      · rintro ⟨h, _⟩; exact h
    · dsimp only
      rw [if_neg hq]
      simp only [Option.map_none, Option.map_some]
      constructor
      · intro h; cases h
      · rintro ⟨h, hk⟩
        have : e2 = b := Option.some.inj h
        subst this
        exact absurd hk hq

/-- State lookup on the pruned store: the original entry, exactly when
pruning keeps it. -/
theorem getState?_prune_iff {st : Store}
    (hnd : (st.states.map (·.1)).Nodup) (r : Root) (s : State) :
    (prune st).getState? r = some s ↔
      st.getState? r = some s ∧ keepState st (r, s) = true := by
  unfold getState?
  rw [prune_states, assocFind?_filter (keepState st) r st.states hnd]
  cases hf : st.states.find? (fun p => p.1 == r) with
  | none => simp
  | some e =>
    obtain ⟨e1, e2⟩ := e
    have he1 : e1 = r := eq_of_beq
      (List.find?_some (p := fun (p : Root × State) => p.1 == r) hf)
    subst he1
    by_cases hq : keepState st (e1, e2) = true
    · dsimp only
      rw [if_pos hq]
      simp only [Option.map_some, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨rfl, hq⟩
      · rintro ⟨h, _⟩; exact h
    · dsimp only
      rw [if_neg hq]
      simp only [Option.map_none, Option.map_some]
      constructor
      · intro h; cases h
      · rintro ⟨h, hk⟩
        have : e2 = s := Option.some.inj h
        subst this
        exact absurd hk hq

/-! ## Walk soundness and the finalized subtree -/

/-- Soundness of the ancestor walk: success exhibits the relational
ancestry, plus the ancestor's stored block sitting at the checkpoint's
slot (the converse of `ancestorWalk_complete`). -/
theorem ancestorWalk_sound (st : Store) (anc : Checkpoint) :
    ∀ (fuel : Nat) (d : Root),
      ancestorWalk st anc fuel d = true →
      AncestorOrEqual st anc.root d ∧
        ∃ ba, st.getBlock? anc.root = some ba ∧ ba.slot = anc.slot
  | 0, _, h => by cases h
  | fuel + 1, d, h => by
    unfold ancestorWalk at h
    cases hb : st.getBlock? d with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      dsimp only at h
      by_cases hslots : b.slot = anc.slot
      · rw [if_pos hslots] at h
        have hd : d = anc.root := eq_of_beq h
        subst hd
        exact ⟨.inl rfl, b, hb, hslots⟩
      · rw [if_neg hslots] at h
        by_cases hbelow : b.slot < anc.slot
        · rw [if_pos hbelow] at h; cases h
        · rw [if_neg hbelow] at h
          obtain ⟨hanc, hba⟩ := ancestorWalk_sound st anc fuel b.parentRoot h
          refine ⟨?_, hba⟩
          cases hanc with
          | inl heq => exact .inr (heq ▸ ProperAncestor.step hb)
          | inr hpa => exact .inr (.tail hb hpa)

/-- Every block on the finalized subtree survives pruning: the keep
predicate is the `checkpointIsAncestor` walk, discharged by completeness
from the relational ancestry. -/
theorem keepBlock_of_ancestorOrEqual {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hslot : ba.slot = st.latestFinalized.slot)
    {m : Root} {bm : Block} (hbm : st.getBlock? m = some bm)
    (hanc : AncestorOrEqual st st.latestFinalized.root m) :
    keepBlock st (m, bm) = true := by
  unfold keepBlock
  refine checkpointIsAncestor_of_ancestorOrEqual hwf
    st.latestFinalized ⟨m, bm.slot⟩ hba hslot hbm hanc ?_
  cases hanc with
  | inl heq =>
    rw [heq] at hba
    have hbb : ba = bm := Option.some.inj (hba.symm.trans hbm)
    show st.latestFinalized.slot ≤ bm.slot
    rw [← hbb, hslot]
    exact UInt64.le_refl _
  | inr hpa =>
    show st.latestFinalized.slot ≤ bm.slot
    exact UInt64.le_of_lt
      (hslot ▸ properAncestor_slot_lt hwf hpa ba bm hba hbm)

/-- The relational ancestry from the finalized root transfers to the
pruned store: every block a finalized-subtree derivation touches is
itself on the subtree, hence kept. -/
private theorem properAncestor_prune_aux {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hslot : ba.slot = st.latestFinalized.slot) {a d : Root}
    (h : ProperAncestor st a d)
    (hfa : AncestorOrEqual st st.latestFinalized.root a) :
    ProperAncestor (prune st) a d := by
  induction h with
  | @step d' b hd =>
    -- The descendant extends the subtree membership by one parent step.
    have hfd : AncestorOrEqual st st.latestFinalized.root d' := by
      cases hfa with
      | inl heq => exact .inr (heq ▸ ProperAncestor.step hd)
      | inr hpa => exact .inr (.tail hd hpa)
    have hkeep := keepBlock_of_ancestorOrEqual hwf hba hslot hd hfd
    exact .step
      ((getBlock?_prune_iff hwf.blocksKeysNodup d' b).mpr ⟨hd, hkeep⟩)
  | @tail _ d' b hd hpa ih =>
    have hfd : AncestorOrEqual st st.latestFinalized.root d' := by
      cases hfa with
      | inl heq => exact .inr (heq ▸ ProperAncestor.tail hd hpa)
      | inr hf => exact .inr (hf.trans (.tail hd hpa))
    have hkeep := keepBlock_of_ancestorOrEqual hwf hba hslot hd hfd
    exact .tail
      ((getBlock?_prune_iff hwf.blocksKeysNodup d' b).mpr ⟨hd, hkeep⟩)
      (ih hfa)

/-- The relational ancestry from the finalized root transfers to the
pruned store. -/
theorem properAncestor_prune {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hslot : ba.slot = st.latestFinalized.slot) {d : Root}
    (h : ProperAncestor st st.latestFinalized.root d) :
    ProperAncestor (prune st) st.latestFinalized.root d :=
  properAncestor_prune_aux hwf hba hslot h (.inl rfl)

/-- `ProperAncestor` reads only the block map. -/
private theorem properAncestor_congr {st st' : Store}
    (hblocks : st'.blocks = st.blocks) :
    ∀ {a d : Root}, ProperAncestor st a d → ProperAncestor st' a d := by
  intro a d h
  have hget : ∀ r, st'.getBlock? r = st.getBlock? r := by
    intro r; unfold getBlock?; rw [hblocks]
  induction h with
  | step hd => exact .step ((hget _).trans hd)
  | tail hd _ ih => exact .tail ((hget _).trans hd) ih

/-! ## Pruning preserves the store invariants -/

/-- #71 (invariant half): pruning preserves `WellFormed`. Key uniqueness
and the parent-slot order restrict to any sublist; block/state alignment
holds because a state is kept exactly when its block is; and the
justified anchor survives with its finalized ancestry because the
justified root lies on the finalized subtree (`WellFormed`'s M-1
clause), every node the walk visits descends from the finalized block,
and completeness re-runs the walk inside the pruned store. -/
theorem prune_wellFormed {st : Store} (hwf : WellFormed st) :
    WellFormed (prune st) := by
  -- Unpack the justified-descends walk into relational form.
  have hjd := hwf.justifiedDescendsFromFinalized
  unfold checkpointIsAncestor at hjd
  by_cases hslotle :
      st.latestJustified.slot < st.latestFinalized.slot
  · rw [if_pos hslotle] at hjd; cases hjd
  rw [if_neg hslotle] at hjd
  obtain ⟨hancJ, ba, hba, hbaslot⟩ :=
    ancestorWalk_sound st st.latestFinalized (st.blocks.length + 1)
      st.latestJustified.root hjd
  -- The finalized block keeps itself.
  have hkeepFin : keepBlock st (st.latestFinalized.root, ba) = true :=
    keepBlock_of_ancestorOrEqual hwf hba hbaslot hba (.inl rfl)
  have hbaP : (prune st).getBlock? st.latestFinalized.root = some ba :=
    (getBlock?_prune_iff hwf.blocksKeysNodup _ _).mpr ⟨hba, hkeepFin⟩
  -- The justified block survives pruning.
  obtain ⟨bj, hbj⟩ := Option.isSome_iff_exists.mp hwf.justifiedInBlocks
  have hkeepJ : keepBlock st (st.latestJustified.root, bj) = true :=
    keepBlock_of_ancestorOrEqual hwf hba hbaslot hbj hancJ
  have hbjP : (prune st).getBlock? st.latestJustified.root = some bj :=
    (getBlock?_prune_iff hwf.blocksKeysNodup _ _).mpr ⟨hbj, hkeepJ⟩
  -- Shared clauses.
  have hndB : ((prune st).blocks.map (·.1)).Nodup :=
    ((prune_blocks_sublist st).map (·.1)).nodup hwf.blocksKeysNodup
  have hsubS : (prune st).states.Sublist st.states := by
    rw [prune_states]; exact List.filter_sublist
  have hndS : ((prune st).states.map (·.1)).Nodup :=
    (hsubS.map (·.1)).nodup hwf.statesKeysNodup
  have haligned : ∀ r : Root,
      ((prune st).getBlock? r).isSome ↔ ((prune st).getState? r).isSome := by
    intro r
    constructor
    · intro h
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hb₀, hkeep⟩ := (getBlock?_prune_iff hwf.blocksKeysNodup r b).mp hb
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp
        ((hwf.blocksStatesAligned r).mp (by rw [hb₀]; rfl))
      have hks : keepState st (r, s) = true := by
        unfold keepState; rw [hb₀]; exact hkeep
      rw [Option.isSome_iff_exists]
      exact ⟨s, (getState?_prune_iff hwf.statesKeysNodup r s).mpr ⟨hs, hks⟩⟩
    · intro h
      obtain ⟨s, hs⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨hs₀, hkeep⟩ := (getState?_prune_iff hwf.statesKeysNodup r s).mp hs
      unfold keepState at hkeep
      cases hb₀ : st.getBlock? r with
      | none => rw [hb₀] at hkeep; cases hkeep
      | some b =>
        rw [hb₀] at hkeep
        rw [Option.isSome_iff_exists]
        exact ⟨b, (getBlock?_prune_iff hwf.blocksKeysNodup r b).mpr
          ⟨hb₀, hkeep⟩⟩
  have hparent : ∀ p ∈ (prune st).blocks, ∀ q ∈ (prune st).blocks,
      q.1 = p.2.parentRoot → q.2.slot < p.2.slot := by
    intro p hp q hq hpq
    exact hwf.parentSlotLt p ((prune_blocks_sublist st).mem hp)
      q ((prune_blocks_sublist st).mem hq) hpq
  -- Circularity breaker: a store with the pruned maps whose justified
  -- checkpoint is the finalized one is `WellFormed` outright, giving
  -- walk completeness inside the pruned block map.
  have hfinle : st.latestFinalized.slot ≤ st.latestJustified.slot :=
    UInt64.not_lt.mp hslotle
  let stAux : Store :=
    { prune st with latestJustified := st.latestFinalized }
  have hwfAux : WellFormed stAux := by
    refine ⟨hndB, hndS, haligned, hparent, ?_, ?_⟩
    · rw [Option.isSome_iff_exists]
      exact ⟨ba, hbaP⟩
    · -- The finalized checkpoint is its own ancestor: one walk step.
      show checkpointIsAncestor stAux st.latestFinalized
        st.latestFinalized = true
      unfold checkpointIsAncestor
      rw [if_neg (by simp)]
      unfold ancestorWalk
      rw [show stAux.getBlock? st.latestFinalized.root = some ba from hbaP]
      dsimp only
      rw [if_pos hbaslot]
      exact beq_self_eq_true _
  -- Justified ancestry inside the pruned store, by completeness.
  have hancP : AncestorOrEqual (prune st) st.latestFinalized.root
      st.latestJustified.root := by
    cases hancJ with
    | inl heq => exact .inl heq
    | inr hpa => exact .inr (properAncestor_prune hwf hba hbaslot hpa)
  have hjdP : checkpointIsAncestor (prune st) st.latestFinalized
      st.latestJustified = true := by
    rw [← checkpointIsAncestor_congr (st := prune st) (st' := stAux) rfl]
    refine checkpointIsAncestor_of_ancestorOrEqual hwfAux
      st.latestFinalized st.latestJustified
      (ba := ba) (bd := bj) hbaP ?_ hbjP ?_ ?_
    · exact hbaslot
    · cases hancP with
      | inl heq => exact .inl heq
      | inr hpa =>
        exact .inr
          (properAncestor_congr (st := prune st) (st' := stAux) rfl hpa)
    · exact hfinle
  exact ⟨hndB, hndS, haligned, hparent,
    Option.isSome_iff_exists.mpr ⟨bj, hbjP⟩, hjdP⟩
