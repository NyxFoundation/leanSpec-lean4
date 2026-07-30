/-
Pruning does not change the fork-choice head (observational equivalence,
head half of #71).

`update_head` on the pruned store selects exactly the head the full
store selects. The proof splits along the structure of the walk:

  - **Vote weights agree on the finalized subtree.** A vote whose head
    lies on the subtree credits an identical chain in both stores
    (every ancestor above the anchor slot is itself on the subtree —
    `keepBlock_of_chain`). A vote whose head is off the subtree credits
    only off-subtree blocks in the full store (an on-subtree ancestor
    would put the head on the subtree — `keepBlock_off_chain`) and
    credits nothing in the pruned store, so on-subtree weights match
    (`KeptAgree`, `accumulate_prune_keptAgree`).
  - **The GHOST walk reads only the subtree.** The walk starts at the
    justified anchor (on the subtree by M-1) and children of subtree
    blocks are subtree blocks, so both walks see identical child lists
    (`childrenOf_prune`) and identical weights at every comparison.
  - **Fuel is irrelevant past the subtree size.** Both stores drive
    walks with `blocks.length + 1` fuel, which differs after pruning;
    the walks only visit subtree blocks, so any fuel above the subtree
    size gives the same result (`creditChain_fuel_stable`,
    `ghostWalk_fuel_stable`).

Main theorem: `updateHead_head_prune` — `(updateHead (prune st)).head =
(updateHead st).head` for any `WellFormed` store. The finalized-
checkpoint half of `update_head` (the `descendToSlot` re-derivation) is
follow-up work; it needs the store-finalization monotonicity discussion
of leanEthereum/leanSpec#1176 M-3 because a head state may finalize
below the pruning horizon.
-/

import LeanSpec.Forks.Lstar.Store.Prune
import LeanSpec.Forks.Lstar.Store.IncrementalWeights

namespace LeanSpec.Forks.Lstar
namespace Store

/-! ## Subtree closure -/

/-- A kept block sits at or above the finalized slot (the walk gate). -/
theorem keepBlock_slot_ge {st : Store} {r : Root} {b : Block}
    (hk : keepBlock st (r, b) = true) :
    st.latestFinalized.slot ≤ b.slot := by
  unfold keepBlock checkpointIsAncestor at hk
  by_cases hlt : b.slot < st.latestFinalized.slot
  · rw [if_pos (by exact hlt)] at hk; cases hk
  · exact UInt64.not_lt.mp hlt

/-- A kept block exhibits the relational ancestry from the finalized
root, plus the finalized block at the finalized slot. -/
theorem rel_of_keepBlock {st : Store} {r : Root} {b : Block}
    (hk : keepBlock st (r, b) = true) :
    AncestorOrEqual st st.latestFinalized.root r ∧
      ∃ ba, st.getBlock? st.latestFinalized.root = some ba ∧
        ba.slot = st.latestFinalized.slot := by
  unfold keepBlock checkpointIsAncestor at hk
  by_cases hlt : b.slot < st.latestFinalized.slot
  · rw [if_pos (by exact hlt)] at hk; cases hk
  · rw [if_neg (by exact hlt)] at hk
    exact ancestorWalk_sound st st.latestFinalized (st.blocks.length + 1)
      r hk

/-- Ancestry composes. -/
private theorem ancestorOrEqual_trans {st : Store} {a m d : Root}
    (h1 : AncestorOrEqual st a m) (h2 : AncestorOrEqual st m d) :
    AncestorOrEqual st a d := by
  cases h1 with
  | inl heq =>
    cases h2 with
    | inl heq' => exact .inl (heq.trans heq')
    | inr hpa => exact .inr (heq ▸ hpa)
  | inr hpa =>
    cases h2 with
    | inl heq' => exact .inr (heq' ▸ hpa)
    | inr hpa' => exact .inr (hpa.trans hpa')

/-- Every ancestor of a kept block at or above the finalized slot is
kept: two ancestors of one block are comparable, and sitting below the
finalized block contradicts the slot bound. -/
theorem keepBlock_of_chain {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {h : Root} {bh : Block} (_hh : st.getBlock? h = some bh)
    (hkh : keepBlock st (h, bh) = true)
    {m : Root} {bm : Block} (hm : st.getBlock? m = some bm)
    (hrel : AncestorOrEqual st m h)
    (hslotm : st.latestFinalized.slot ≤ bm.slot) :
    keepBlock st (m, bm) = true := by
  have hfh := (rel_of_keepBlock hkh).1
  cases ancestors_comparable hfh hrel with
  | inl hfm => exact keepBlock_of_ancestorOrEqual hwf hba hbaslot hm hfm
  | inr hmf =>
    exfalso
    have hlt := properAncestor_slot_lt hwf hmf bm ba hm hba
    rw [hbaslot] at hlt
    exact absurd hlt (UInt64.not_lt.mpr hslotm)

/-- No ancestor of an off-subtree block is kept: a kept ancestor would
put the block itself on the subtree. -/
theorem keepBlock_off_chain {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {h : Root} {bh : Block} (hh : st.getBlock? h = some bh)
    (hkh : keepBlock st (h, bh) = false)
    {m : Root} {bm : Block} (_hm : st.getBlock? m = some bm)
    (hrel : AncestorOrEqual st m h) :
    keepBlock st (m, bm) = false := by
  cases hk : keepBlock st (m, bm) with
  | false => rfl
  | true =>
    exfalso
    have hfm := (rel_of_keepBlock hk).1
    have hfh := ancestorOrEqual_trans hfm hrel
    have := keepBlock_of_ancestorOrEqual hwf hba hbaslot hh hfh
    rw [this] at hkh
    cases hkh

/-! ## Pruned lookups, negative direction -/

/-- A root the full store does not know stays unknown after pruning. -/
theorem getBlock?_prune_none_of_none {st : Store}
    (hnd : (st.blocks.map (·.1)).Nodup) {r : Root}
    (h : st.getBlock? r = none) : (prune st).getBlock? r = none := by
  cases hp : (prune st).getBlock? r with
  | none => rfl
  | some b =>
    have := ((getBlock?_prune_iff hnd r b).mp hp).1
    rw [h] at this
    cases this

/-- An off-subtree block is gone after pruning. -/
theorem getBlock?_prune_none_of_notkept {st : Store}
    (hnd : (st.blocks.map (·.1)).Nodup) {r : Root} {b : Block}
    (hb : st.getBlock? r = some b) (hk : keepBlock st (r, b) = false) :
    (prune st).getBlock? r = none := by
  cases hp : (prune st).getBlock? r with
  | none => rfl
  | some b' =>
    obtain ⟨hb', hk'⟩ := (getBlock?_prune_iff hnd r b').mp hp
    have : b = b' := Option.some.inj (hb.symm.trans hb')
    rw [← this] at hk'
    rw [hk'] at hk
    cases hk

/-! ## Chain-credit plumbing -/

/-- The credit climb from an unknown root is a no-op, at any fuel. -/
private theorem creditChain_none {st : Store} {s : Slot} {r : Root}
    (h : st.getBlock? r = none) :
    ∀ (fuel : Nat) (w : Weights), creditChain st s fuel r w = w
  | 0, _ => rfl
  | _ + 1, w => by unfold creditChain; rw [h]

/-- The credit climb from a block at or below the anchor slot is a
no-op, at any fuel. -/
private theorem creditChain_stop {st : Store} {s : Slot} {r : Root}
    {b : Block} (h : st.getBlock? r = some b) (hle : b.slot ≤ s) :
    ∀ (fuel : Nat) (w : Weights), creditChain st s fuel r w = w
  | 0, _ => rfl
  | _ + 1, w => by
    unfold creditChain
    rw [h]
    dsimp only
    rw [if_pos hle]

/-- Weight maps agreeing on every kept root. -/
def KeptAgree (st : Store) (w₁ w₂ : Weights) : Prop :=
  ∀ r b, st.getBlock? r = some b → keepBlock st (r, b) = true →
    w₁.get r = w₂.get r

/-- A climb from an off-subtree head never moves a kept root's weight:
every bumped block is an ancestor of the head, hence off the subtree. -/
private theorem creditChain_get_off {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {h : Root} {bh : Block} (hh : st.getBlock? h = some bh)
    (hkh : keepBlock st (h, bh) = false) (s : Slot) :
    ∀ (fuel : Nat) (cur : Root) (w : Weights),
      AncestorOrEqual st cur h →
      ∀ (x : Root) (bx : Block), st.getBlock? x = some bx →
        keepBlock st (x, bx) = true →
        (creditChain st s fuel cur w).get x = w.get x
  | 0, _, _, _, _, _, _, _ => rfl
  | fuel + 1, cur, w, hrel, x, bx, hx, hkx => by
    unfold creditChain
    cases hbc : st.getBlock? cur with
    | none => rfl
    | some bcur =>
      dsimp only
      by_cases hle : bcur.slot ≤ s
      · rw [if_pos hle]
      · rw [if_neg hle]
        have hrel' : AncestorOrEqual st bcur.parentRoot h :=
          ancestorOrEqual_trans (.inr (ProperAncestor.step hbc)) hrel
        rw [creditChain_get_off hwf hba hbaslot hh hkh s fuel
          bcur.parentRoot (w.bump cur) hrel' x bx hx hkx]
        rw [Weights.get_bump]
        have hxc : ¬x = cur := by
          intro heq
          subst heq
          have : bx = bcur := Option.some.inj (hx.symm.trans hbc)
          subst this
          have hoff := keepBlock_off_chain hwf hba hbaslot hh hkh hbc hrel
          rw [hoff] at hkx
          cases hkx
        rw [if_neg hxc]
        omega

/-- A climb from a subtree head visits only subtree blocks, at slots
strictly above the anchor: the pruned store retraces it step for step,
preserving kept-root agreement of the accumulators. -/
private theorem creditChain_prune_keptAgree {st : Store}
    (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {h : Root} {bh : Block} (hh : st.getBlock? h = some bh)
    (hkh : keepBlock st (h, bh) = true)
    {s : Slot} (hs : st.latestFinalized.slot ≤ s) :
    ∀ (fuel : Nat) (cur : Root) (bcur : Block),
      st.getBlock? cur = some bcur → keepBlock st (cur, bcur) = true →
      AncestorOrEqual st cur h →
      ∀ (w₁ w₂ : Weights), KeptAgree st w₁ w₂ →
      KeptAgree st (creditChain (prune st) s fuel cur w₁)
        (creditChain st s fuel cur w₂)
  | 0, _, _, _, _, _, _, _, hw => hw
  | fuel + 1, cur, bcur, hcur, hkcur, hrel, w₁, w₂, hw => by
    have hcurP : (prune st).getBlock? cur = some bcur :=
      (getBlock?_prune_iff hwf.blocksKeysNodup cur bcur).mpr ⟨hcur, hkcur⟩
    unfold creditChain
    rw [hcur, hcurP]
    dsimp only
    by_cases hle : bcur.slot ≤ s
    · rw [if_pos hle, if_pos hle]; exact hw
    · rw [if_neg hle, if_neg hle]
      have hw' : KeptAgree st (w₁.bump cur) (w₂.bump cur) := by
        intro r b hb hk
        rw [Weights.get_bump, Weights.get_bump, hw r b hb hk]
      cases hp : st.getBlock? bcur.parentRoot with
      | none =>
        rw [creditChain_none hp, creditChain_none
          (getBlock?_prune_none_of_none hwf.blocksKeysNodup hp)]
        exact hw'
      | some bp =>
        have hrelp : AncestorOrEqual st bcur.parentRoot h :=
          ancestorOrEqual_trans (.inr (ProperAncestor.step hcur)) hrel
        by_cases hps : bp.slot ≤ s
        · rw [creditChain_stop hp hps]
          cases hpp : (prune st).getBlock? bcur.parentRoot with
          | none => rw [creditChain_none hpp]; exact hw'
          | some bp' =>
            have hbp' :=
              ((getBlock?_prune_iff hwf.blocksKeysNodup _ bp').mp hpp).1
            have : bp = bp' := Option.some.inj (hp.symm.trans hbp')
            subst this
            rw [creditChain_stop hpp hps]
            exact hw'
        · have hfinp : st.latestFinalized.slot ≤ bp.slot :=
            UInt64.le_of_lt
              (UInt64.lt_of_le_of_lt hs (UInt64.not_le.mp hps))
          have hkp : keepBlock st (bcur.parentRoot, bp) = true :=
            keepBlock_of_chain hwf hba hbaslot hh hkh hp hrelp hfinp
          exact creditChain_prune_keptAgree hwf hba hbaslot hh hkh hs
            fuel bcur.parentRoot bp hp hkp hrelp _ _ hw'

/-! ## Fuel stability on subtree walks -/

/-- Kept blocks at or below a slot: the decreasing measure of the credit
climb. -/
private def keptBelow (st : Store) (s : Slot) : Nat :=
  (st.blocks.filter
    (fun p => keepBlock st p && decide (p.2.slot ≤ s))).length

/-- Kept blocks strictly above a slot: the decreasing measure of the
GHOST descent. -/
private def keptAbove (st : Store) (s : Slot) : Nat :=
  (st.blocks.filter
    (fun p => keepBlock st p && decide (s < p.2.slot))).length

/-- Filtering by a stronger predicate never yields a longer list. -/
private theorem filter_length_mono' {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      (l.filter p).length ≤ (l.filter q).length
  | [], _ => Nat.le_refl _
  | x :: t, himp => by
    have ht := filter_length_mono' p q t
      (fun y hy => himp y (List.mem_cons_of_mem x hy))
    cases hp : p x with
    | true =>
      rw [List.filter_cons_of_pos hp,
        List.filter_cons_of_pos (himp x List.mem_cons_self hp)]
      exact Nat.succ_le_succ ht
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp])]
      cases hq : q x with
      | true =>
        rw [List.filter_cons_of_pos hq]
        exact Nat.le_succ_of_le ht
      | false =>
        rw [List.filter_cons_of_neg (by simp [hq])]
        exact ht

/-- A member kept by `q` but dropped by `p` makes the `p`-filter
strictly shorter. -/
private theorem filter_length_lt' {α : Type} (p q : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true → q x = true) →
      ∀ w ∈ l, q w = true → p w = false →
      (l.filter p).length < (l.filter q).length
  | [], _, w, hw, _, _ => absurd hw List.not_mem_nil
  | x :: t, himp, w, hw, hqw, hpw => by
    have himpt : ∀ y ∈ t, p y = true → q y = true :=
      fun y hy => himp y (List.mem_cons_of_mem x hy)
    cases List.mem_cons.mp hw with
    | inl hwx =>
      subst hwx
      rw [List.filter_cons_of_neg (by simp [hpw]),
        List.filter_cons_of_pos hqw]
      exact Nat.lt_succ_of_le (filter_length_mono' p q t himpt)
    | inr hwt =>
      have ht := filter_length_lt' p q t himpt w hwt hqw hpw
      cases hp : p x with
      | true =>
        rw [List.filter_cons_of_pos hp,
          List.filter_cons_of_pos (himp x List.mem_cons_self hp)]
        exact Nat.succ_lt_succ ht
      | false =>
        rw [List.filter_cons_of_neg (by simp [hp])]
        cases hq : q x with
        | true =>
          rw [List.filter_cons_of_pos hq]
          exact Nat.lt_succ_of_lt ht
        | false =>
          rw [List.filter_cons_of_neg (by simp [hq])]
          exact ht

/-- Both subtree measures are bounded by the pruned store size. -/
private theorem keptBelow_le (st : Store) (s : Slot) :
    keptBelow st s ≤ (prune st).blocks.length := by
  rw [prune_blocks]
  exact filter_length_mono' _ _ st.blocks
    (fun x _ hx => ((Bool.and_eq_true ..).mp hx).1)

private theorem keptAbove_le (st : Store) (s : Slot) :
    keptAbove st s ≤ (prune st).blocks.length := by
  rw [prune_blocks]
  exact filter_length_mono' _ _ st.blocks
    (fun x _ hx => ((Bool.and_eq_true ..).mp hx).1)

/-- The credit climb from a kept block gives the same result at any two
sufficient fuels: it visits only kept blocks at strictly decreasing
slots, so `keptBelow` bounds its length. -/
private theorem creditChain_fuel_stable {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {s : Slot} (hs : st.latestFinalized.slot ≤ s) :
    ∀ (f₁ f₂ : Nat) (cur : Root) (bcur : Block),
      st.getBlock? cur = some bcur → keepBlock st (cur, bcur) = true →
      keptBelow st bcur.slot < f₁ → keptBelow st bcur.slot < f₂ →
      ∀ (w : Weights),
        creditChain st s f₁ cur w = creditChain st s f₂ cur w
  | 0, _, _, bcur, hcur, hkcur, h1, _, _ => by
    exfalso
    have hmem := getBlock?_eq_some_mem hcur
    have : 0 < keptBelow st bcur.slot := by
      apply List.length_pos_of_mem
      refine List.mem_filter.mpr ⟨hmem, ?_⟩
      exact (Bool.and_eq_true ..).mpr
        ⟨hkcur, decide_eq_true (UInt64.le_refl _)⟩
    omega
  | _ + 1, 0, _, bcur, hcur, hkcur, _, h2, _ => by
    exfalso
    have hmem := getBlock?_eq_some_mem hcur
    have : 0 < keptBelow st bcur.slot := by
      apply List.length_pos_of_mem
      refine List.mem_filter.mpr ⟨hmem, ?_⟩
      exact (Bool.and_eq_true ..).mpr
        ⟨hkcur, decide_eq_true (UInt64.le_refl _)⟩
    omega
  | f₁ + 1, f₂ + 1, cur, bcur, hcur, hkcur, h1, h2, w => by
    unfold creditChain
    rw [hcur]
    dsimp only
    by_cases hle : bcur.slot ≤ s
    · rw [if_pos hle, if_pos hle]
    · rw [if_neg hle, if_neg hle]
      cases hp : st.getBlock? bcur.parentRoot with
      | none => rw [creditChain_none hp, creditChain_none hp]
      | some bp =>
        by_cases hps : bp.slot ≤ s
        · rw [creditChain_stop hp hps, creditChain_stop hp hps]
        · have hfinp : st.latestFinalized.slot ≤ bp.slot :=
            UInt64.le_of_lt
              (UInt64.lt_of_le_of_lt hs (UInt64.not_le.mp hps))
          have hkp : keepBlock st (bcur.parentRoot, bp) = true :=
            keepBlock_of_chain hwf hba hbaslot hcur hkcur hp
              (.inr (ProperAncestor.step hcur)) hfinp
          have hplt : bp.slot < bcur.slot :=
            hwf.parentSlotLt (cur, bcur) (getBlock?_eq_some_mem hcur)
              (bcur.parentRoot, bp) (getBlock?_eq_some_mem hp) rfl
          have hdec : keptBelow st bp.slot < keptBelow st bcur.slot := by
            apply filter_length_lt' _ _ st.blocks
            · intro x _ hx
              obtain ⟨hk, hd⟩ := (Bool.and_eq_true ..).mp hx
              refine (Bool.and_eq_true ..).mpr ⟨hk, decide_eq_true ?_⟩
              exact UInt64.le_trans (of_decide_eq_true hd)
                (UInt64.le_of_lt hplt)
            · exact getBlock?_eq_some_mem hcur
            · exact (Bool.and_eq_true ..).mpr
                ⟨hkcur, decide_eq_true (UInt64.le_refl _)⟩
            · refine (Bool.and_eq_false_iff ..).mpr (Or.inr ?_)
              exact decide_eq_false (UInt64.not_le.mpr hplt)
          exact creditChain_fuel_stable hwf hba hbaslot hs f₁ f₂
            bcur.parentRoot bp hp hkp (by omega) (by omega) (w.bump cur)

/-! ## Children and the GHOST walk across pruning -/

/-- Children of a subtree block are the same list in both stores: every
child of a kept block is kept, so the prune filter is transparent to
the child filter (order preserved). No `minScore`, as in
`update_head`. -/
private theorem childrenOf_prune {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    (w₁ w₂ : Weights) {parent : Root} {bp : Block}
    (_hp : st.getBlock? parent = some bp)
    (hkp : keepBlock st (parent, bp) = true) :
    childrenOf (prune st) w₁ none parent = childrenOf st w₂ none parent := by
  unfold childrenOf
  rw [prune_blocks, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro x hx
  dsimp only
  cases hpar : (x.2.parentRoot == parent) with
  | false => simp
  | true =>
    have hxb : st.getBlock? x.1 = some x.2 :=
      getBlock?_eq_some_of_mem hwf.blocksKeysNodup hx
    have hrel : AncestorOrEqual st parent x.1 :=
      .inr (eq_of_beq hpar ▸ ProperAncestor.step hxb)
    have hkx : keepBlock st (x.1, x.2) = true :=
      keepBlock_of_ancestorOrEqual hwf hba hbaslot hxb
        (ancestorOrEqual_trans (rel_of_keepBlock hkp).1 hrel)
    simp [hkx]

/-- The child pick agrees when the weights agree on the seed and every
candidate. -/
private theorem foldl_pick_agree {w₁ w₂ : Weights} :
    ∀ (cs : List Root) (a : Root),
      (∀ y, y = a ∨ y ∈ cs → w₁.get y = w₂.get y) →
      cs.foldl (fun best cand =>
        if beats w₁ best cand then cand else best) a
        = cs.foldl (fun best cand =>
          if beats w₂ best cand then cand else best) a
  | [], _, _ => rfl
  | c :: cs, a, hy => by
    rw [List.foldl_cons, List.foldl_cons]
    have hbeats : beats w₁ a c = beats w₂ a c := by
      unfold beats
      rw [hy a (Or.inl rfl), hy c (Or.inr List.mem_cons_self)]
    rw [hbeats]
    by_cases hb : beats w₂ a c = true
    · rw [if_pos hb]
      exact foldl_pick_agree cs c (fun y hyy => hy y (by
        cases hyy with
        | inl h => exact Or.inr (h ▸ List.mem_cons_self)
        | inr h => exact Or.inr (List.mem_cons_of_mem c h)))
    · rw [if_neg hb]
      exact foldl_pick_agree cs a (fun y hyy => hy y (by
        cases hyy with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (List.mem_cons_of_mem c h)))

/-- The winning child agrees when the weights agree on every candidate. -/
private theorem maxChild_agree {w₁ w₂ : Weights} (cs : List Root)
    (hcs : ∀ c ∈ cs, w₁.get c = w₂.get c) :
    maxChild w₁ cs = maxChild w₂ cs := by
  cases cs with
  | nil => rfl
  | cons c t =>
    unfold maxChild
    dsimp only
    rw [foldl_pick_agree t c (fun y hy => by
      cases hy with
      | inl h => exact hcs y (h ▸ List.mem_cons_self)
      | inr h => exact hcs y (List.mem_cons_of_mem c h))]

/-- The GHOST descent from a subtree anchor is identical in both stores
at equal fuel: child lists match and all read weights agree. -/
private theorem ghostWalk_prune {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {w₁ w₂ : Weights} (hw : KeptAgree st w₁ w₂) :
    ∀ (fuel : Nat) (r : Root) (br : Block),
      st.getBlock? r = some br → keepBlock st (r, br) = true →
      ghostWalk (prune st) w₁ none fuel r = ghostWalk st w₂ none fuel r
  | 0, _, _, _, _ => rfl
  | fuel + 1, r, br, hr, hkr => by
    unfold ghostWalk
    rw [childrenOf_prune hwf hba hbaslot w₁ w₂ hr hkr]
    have hkids : ∀ c ∈ childrenOf st w₂ none r,
        ∃ bc, st.getBlock? c = some bc ∧ keepBlock st (c, bc) = true := by
      intro c hc
      obtain ⟨bc, hbc, hpar⟩ :=
        childrenOf_parent st w₂ none r c hwf.blocksKeysNodup hc
      refine ⟨bc, hbc, ?_⟩
      exact keepBlock_of_ancestorOrEqual hwf hba hbaslot hbc
        (ancestorOrEqual_trans (rel_of_keepBlock hkr).1
          (.inr (hpar ▸ ProperAncestor.step hbc)))
    rw [maxChild_agree (childrenOf st w₂ none r) (fun c hc => by
      obtain ⟨bc, hbc, hkc⟩ := hkids c hc
      exact hw c bc hbc hkc)]
    cases hmc : maxChild w₂ (childrenOf st w₂ none r) with
    | none => rfl
    | some best =>
      obtain ⟨bb, hbb, hkb⟩ :=
        hkids best (maxChild_mem w₂ _ best hmc)
      exact ghostWalk_prune hwf hba hbaslot hw fuel best bb hbb hkb

/-- The GHOST descent from a subtree anchor gives the same result at any
two sufficient fuels: it visits only kept blocks at strictly increasing
slots, so `keptAbove` bounds its length. -/
private theorem ghostWalk_fuel_stable {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot) (w : Weights) :
    ∀ (f₁ f₂ : Nat) (r : Root) (br : Block),
      st.getBlock? r = some br → keepBlock st (r, br) = true →
      keptAbove st br.slot < f₁ → keptAbove st br.slot < f₂ →
      ghostWalk st w none f₁ r = ghostWalk st w none f₂ r
  | 0, _, _, _, _, _, h1, _ => by
    exact absurd h1 (by omega)
  | _ + 1, 0, _, _, _, _, _, h2 => by
    exact absurd h2 (by omega)
  | f₁ + 1, f₂ + 1, r, br, hr, hkr, h1, h2 => by
    unfold ghostWalk
    cases hmc : maxChild w (childrenOf st w none r) with
    | none => rfl
    | some best =>
      obtain ⟨bb, hbb, hpar⟩ := childrenOf_parent st w none r best
        hwf.blocksKeysNodup (maxChild_mem w _ best hmc)
      have hkb : keepBlock st (best, bb) = true :=
        keepBlock_of_ancestorOrEqual hwf hba hbaslot hbb
          (ancestorOrEqual_trans (rel_of_keepBlock hkr).1
            (.inr (hpar ▸ ProperAncestor.step hbb)))
      have hslt : br.slot < bb.slot :=
        hwf.parentSlotLt (best, bb) (getBlock?_eq_some_mem hbb)
          (r, br) (getBlock?_eq_some_mem hr) (by rw [hpar])
      have hdec : keptAbove st bb.slot < keptAbove st br.slot := by
        apply filter_length_lt' _ _ st.blocks
        · intro x _ hx
          obtain ⟨hk, hd⟩ := (Bool.and_eq_true ..).mp hx
          refine (Bool.and_eq_true ..).mpr ⟨hk, decide_eq_true ?_⟩
          exact UInt64.lt_trans hslt (of_decide_eq_true hd)
        · exact getBlock?_eq_some_mem hbb
        · exact (Bool.and_eq_true ..).mpr ⟨hkb, decide_eq_true hslt⟩
        · refine (Bool.and_eq_false_iff ..).mpr (Or.inr ?_)
          exact decide_eq_false (UInt64.lt_irrefl _)
      exact ghostWalk_fuel_stable hwf hba hbaslot w f₁ f₂ best bb hbb hkb
        (by omega) (by omega)

/-! ## Weight agreement over the vote fold -/

/-- The full tallies agree on every kept root, across the two stores and
their respective fuels. -/
private theorem accumulate_prune_keptAgree {st : Store}
    (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {s : Slot} (hs : st.latestFinalized.slot ≤ s) :
    ∀ (votes : List (Nat × AttestationData)) (w₁ w₂ : Weights),
      KeptAgree st w₁ w₂ →
      KeptAgree st
        (votes.foldl (fun w att => creditChain (prune st) s
          ((prune st).blocks.length + 1) att.2.head.root w) w₁)
        (votes.foldl (fun w att => creditChain st s
          (st.blocks.length + 1) att.2.head.root w) w₂)
  | [], _, _, hw => hw
  | v :: votes, w₁, w₂, hw => by
    rw [List.foldl_cons, List.foldl_cons]
    refine accumulate_prune_keptAgree hwf hba hbaslot hs votes _ _ ?_
    cases hv : st.getBlock? v.2.head.root with
    | none =>
      rw [creditChain_none hv, creditChain_none
        (getBlock?_prune_none_of_none hwf.blocksKeysNodup hv)]
      exact hw
    | some bh =>
      by_cases hk : keepBlock st (v.2.head.root, bh) = true
      · have h9 := creditChain_prune_keptAgree hwf hba hbaslot hv hk hs
          ((prune st).blocks.length + 1) v.2.head.root bh hv hk (.inl rfl)
          w₁ w₂ hw
        have hstab := creditChain_fuel_stable hwf hba hbaslot hs
          ((prune st).blocks.length + 1) (st.blocks.length + 1)
          v.2.head.root bh hv hk
          (Nat.lt_succ_of_le (keptBelow_le st bh.slot))
          (Nat.lt_succ_of_le (Nat.le_trans (keptBelow_le st bh.slot)
            ((prune_blocks_sublist st).length_le)))
          w₂
        rw [← hstab]
        exact h9
      · have hkf : keepBlock st (v.2.head.root, bh) = false := by
          cases hkk : keepBlock st (v.2.head.root, bh) with
          | false => rfl
          | true => exact absurd hkk hk
        rw [creditChain_none
          (getBlock?_prune_none_of_notkept hwf.blocksKeysNodup hv hkf)]
        intro r b hb hkb
        rw [creditChain_get_off hwf hba hbaslot hv hkf s
          (st.blocks.length + 1) v.2.head.root w₂ (.inl rfl) r b hb hkb]
        exact hw r b hb hkb

/-! ## Head equivalence -/

/-- The LMD-GHOST head from any subtree anchor is unchanged by pruning. -/
theorem computeLmdGhostHead_prune {st : Store} (hwf : WellFormed st)
    {ba : Block} (hba : st.getBlock? st.latestFinalized.root = some ba)
    (hbaslot : ba.slot = st.latestFinalized.slot)
    {r : Root} {br : Block} (hr : st.getBlock? r = some br)
    (hkr : keepBlock st (r, br) = true)
    (votes : List (Nat × AttestationData)) :
    computeLmdGhostHead (prune st) r votes none
      = computeLmdGhostHead st r votes none := by
  unfold computeLmdGhostHead
  have hrP : (prune st).getBlock? r = some br :=
    (getBlock?_prune_iff hwf.blocksKeysNodup r br).mpr ⟨hr, hkr⟩
  rw [hr, hrP]
  dsimp only
  have hs : st.latestFinalized.slot ≤ br.slot := keepBlock_slot_ge hkr
  have hw : KeptAgree st
      (accumulateAncestorWeights (prune st) votes br.slot)
      (accumulateAncestorWeights st votes br.slot) :=
    accumulate_prune_keptAgree hwf hba hbaslot hs votes [] []
      (fun _ _ _ _ => rfl)
  rw [ghostWalk_prune hwf hba hbaslot hw ((prune st).blocks.length + 1)
    r br hr hkr]
  exact ghostWalk_fuel_stable hwf hba hbaslot _
    ((prune st).blocks.length + 1) (st.blocks.length + 1) r br hr hkr
    (Nat.lt_succ_of_le (keptAbove_le st br.slot))
    (Nat.lt_succ_of_le (Nat.le_trans (keptAbove_le st br.slot)
      ((prune_blocks_sublist st).length_le)))

/-- #71 (head half of the observational equivalence): pruning below the
finalized root never changes the fork-choice head. The walk anchors at
the justified root, which sits on the finalized subtree (M-1), and the
whole computation — vote tally, child enumeration, comparisons,
tie-break — reads only subtree blocks, which pruning keeps. -/
theorem updateHead_head_prune [SSZ.HasHashTreeRoot AttestationData]
    {st : Store} (hwf : WellFormed st) :
    (updateHead (prune st)).head = (updateHead st).head := by
  -- Subtree facts for the justified anchor.
  obtain ⟨bj, hbj⟩ := Option.isSome_iff_exists.mp hwf.justifiedInBlocks
  have hjd := hwf.justifiedDescendsFromFinalized
  unfold checkpointIsAncestor at hjd
  by_cases hslotle : st.latestJustified.slot < st.latestFinalized.slot
  · rw [if_pos hslotle] at hjd; cases hjd
  rw [if_neg hslotle] at hjd
  obtain ⟨hancJ, ba, hba, hbaslot⟩ :=
    ancestorWalk_sound st st.latestFinalized (st.blocks.length + 1)
      st.latestJustified.root hjd
  have hkj : keepBlock st (st.latestJustified.root, bj) = true :=
    keepBlock_of_ancestorOrEqual hwf hba hbaslot hbj hancJ
  show computeLmdGhostHead (prune st) (prune st).latestJustified.root
      (extractAttestationsFromAggregatedPayloads
        (prune st).latestKnownAggregatedPayloads
        (prune st).latestFinalized.slot) none
    = computeLmdGhostHead st st.latestJustified.root
      (extractAttestationsFromAggregatedPayloads
        st.latestKnownAggregatedPayloads st.latestFinalized.slot) none
  exact computeLmdGhostHead_prune hwf hba hbaslot hbj hkj _

end Store
end LeanSpec.Forks.Lstar
