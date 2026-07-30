/-
Incremental (proto-array-style) weight maintenance agrees with the
naive re-tally.

Upstream's `_compute_lmd_ghost_head` re-tallies every vote on every call
(`_accumulate_ancestor_weights` folded over the full LMD view).
Production clients instead maintain the weight map incrementally: when
the vote set changes, only the delta (votes added, votes removed is
handled by re-extraction here — the LMD view is always a function of the
pool) is credited. Issue #67 asks for the refinement theorem making that
optimization a conformance target.

This file proves the algebraic core of that refinement:

  - `Weights.Equiv` — extensional equality of weight maps (`get`-equal;
    association lists differing in entry order or zero entries are the
    same weight function).
  - `creditChain_get_add` / `accumulateAncestorWeights_append` — the
    tally is **pointwise additive**: crediting a batch is the pointwise
    sum of crediting its parts. This is exactly the property that makes
    per-vote weight *deltas* well-defined.
  - `accumulateAncestorWeights_perm` — the tally is **order-free**: any
    permutation of the vote list yields the same weight function, so an
    incremental maintainer may apply vote updates in any order.
  - `ghostWalk_congr_weights` / `computeLmdGhostHead_congr_weights` —
    the GHOST descent reads weights only through `get`, so extensionally
    equal weight maps select the same head (tie-break included).

Together: a client that maintains weights incrementally — in any order,
batching however it likes — computes the same head as the naive spec
walk, provided its maintained map is `get`-equal to the full tally.
The best-child/best-descendant cache layer of proto-array sits on top
and is follow-up work; its correctness reduces to the walk over the
same weight function proved here.
-/

import LeanSpec.Forks.Lstar.Store.Ancestry

namespace LeanSpec.Forks.Lstar
namespace Store

namespace Weights

/-- Extensional equality of weight maps: equal weight on every root.
Association lists differing in order or explicit zeros are identified. -/
def Equiv (w w' : Weights) : Prop := ∀ r : Root, w.get r = w'.get r

theorem Equiv.refl (w : Weights) : Equiv w w := fun _ => rfl

theorem Equiv.symm {w w' : Weights} (h : Equiv w w') : Equiv w' w :=
  fun r => (h r).symm

theorem Equiv.trans {w₁ w₂ w₃ : Weights} (h1 : Equiv w₁ w₂)
    (h2 : Equiv w₂ w₃) : Equiv w₁ w₃ :=
  fun r => (h1 r).trans (h2 r)

/-- `find?` skips entries whose key differs from the searched root. -/
private theorem find?_filter_ne (w : Weights) (r x : Root) (hxr : ¬x = r) :
    (w.filter (fun q => !(q.1 == r))).find? (fun p => p.1 == x)
      = w.find? (fun p => p.1 == x) := by
  induction w with
  | nil => rfl
  | cons a t ih =>
    by_cases har : a.1 = r
    · have hnax : ¬a.1 = x := fun hax => hxr (by rw [← hax, har])
      rw [List.filter_cons]
      rw [if_neg (by simp [har])]
      rw [List.find?_cons_of_neg (by simp [hnax]), ih]
    · rw [List.filter_cons]
      rw [if_pos (by simp [har])]
      by_cases hax : a.1 = x
      · rw [List.find?_cons_of_pos (by simp [hax]),
          List.find?_cons_of_pos (by simp [hax])]
      · rw [List.find?_cons_of_neg (by simp [hax]),
          List.find?_cons_of_neg (by simp [hax]), ih]

/-- `bump` adds exactly one to the bumped root and nothing elsewhere. -/
theorem get_bump (w : Weights) (r x : Root) :
    (w.bump r).get x = w.get x + (if x = r then 1 else 0) := by
  unfold bump
  cases hf : w.find? (fun p => p.1 == r) with
  | some p =>
    by_cases hxr : x = r
    · subst hxr
      unfold get
      rw [List.find?_cons_of_pos (by simp)]
      simp only [Option.map_some, Option.getD_some]
      rw [hf]; rfl
    · unfold get
      have hnrx : ¬(r = x) := fun h => hxr h.symm
      rw [List.find?_cons_of_neg (by simp [hnrx]),
        find?_filter_ne w r x hxr]
      simp [hxr]
  | none =>
    by_cases hxr : x = r
    · subst hxr
      unfold get
      rw [List.find?_cons_of_pos (by simp)]
      simp only [Option.map_some, Option.getD_some]
      rw [hf]; rfl
    · unfold get
      have hnrx : ¬(r = x) := fun h => hxr h.symm
      rw [List.find?_cons_of_neg (by simp [hnrx])]
      simp [hxr]

end Weights

/-- The chain credit is pointwise additive over its accumulator: crediting
on top of `w` reads as `w` plus crediting from empty. This is the exact
algebraic fact that makes per-vote weight deltas well-defined. -/
theorem creditChain_get_add (st : Store) (s : Slot) :
    ∀ (fuel : Nat) (r : Root) (w : Weights) (x : Root),
      (creditChain st s fuel r w).get x
        = w.get x + (creditChain st s fuel r []).get x
  | 0, _, _, _ => rfl
  | fuel + 1, r, w, x => by
    have h0 : Weights.get ([] : Weights) x = 0 := rfl
    unfold creditChain
    cases hb : st.getBlock? r with
    | none => dsimp only; omega
    | some b =>
      dsimp only
      by_cases hle : b.slot ≤ s
      · rw [if_pos hle, if_pos hle]; omega
      · rw [if_neg hle, if_neg hle]
        have h1 := creditChain_get_add st s fuel b.parentRoot (w.bump r) x
        have h2 := creditChain_get_add st s fuel b.parentRoot
          (Weights.bump [] r) x
        have h3 := Weights.get_bump w r x
        have h4 := Weights.get_bump [] r x
        omega

/-- Folding the credit step over a batch on top of any accumulator reads
as the accumulator plus folding from empty. -/
private theorem tallyFold_get_add (st : Store) (s : Slot) :
    ∀ (l : List (Nat × AttestationData)) (w : Weights) (x : Root),
      (l.foldl (fun w att =>
        creditChain st s (st.blocks.length + 1) att.2.head.root w) w).get x
      = w.get x + (l.foldl (fun w att =>
        creditChain st s (st.blocks.length + 1) att.2.head.root w) []).get x
  | [], w, x => by
    have h0 : Weights.get ([] : Weights) x = 0 := rfl
    dsimp only [List.foldl_nil]
    omega
  | v :: t, w, x => by
    rw [List.foldl_cons, List.foldl_cons]
    have h1 := tallyFold_get_add st s t
      (creditChain st s (st.blocks.length + 1) v.2.head.root w) x
    have h2 := tallyFold_get_add st s t
      (creditChain st s (st.blocks.length + 1) v.2.head.root []) x
    have h3 := creditChain_get_add st s (st.blocks.length + 1)
      v.2.head.root w x
    omega

/-- The batch tally is pointwise additive: tallying `a ++ b` is the
pointwise sum of tallying each part. An incremental maintainer may
therefore credit any new batch on top of an existing tally — the
algebraic fact that makes per-vote weight *deltas* well-defined. -/
theorem accumulateAncestorWeights_append (st : Store)
    (a b : List (Nat × AttestationData)) (s : Slot) (x : Root) :
    (accumulateAncestorWeights st (a ++ b) s).get x
      = (accumulateAncestorWeights st a s).get x
        + (accumulateAncestorWeights st b s).get x := by
  unfold accumulateAncestorWeights
  rw [List.foldl_append]
  exact tallyFold_get_add st s b _ x

/-- Prepending one vote adds its chain credit pointwise. -/
private theorem accumulate_cons_get (st : Store)
    (v : Nat × AttestationData) (l : List (Nat × AttestationData))
    (s : Slot) (x : Root) :
    (accumulateAncestorWeights st (v :: l) s).get x
      = (accumulateAncestorWeights st [v] s).get x
        + (accumulateAncestorWeights st l s).get x := by
  have h := accumulateAncestorWeights_append st [v] l s x
  simpa using h

/-- The tally is order-free: permuting the vote list leaves the weight of
every root unchanged, so incremental updates may be applied in any
order. -/
theorem accumulateAncestorWeights_perm (st : Store)
    {a b : List (Nat × AttestationData)} (hperm : a.Perm b) (s : Slot)
    (x : Root) :
    (accumulateAncestorWeights st a s).get x
      = (accumulateAncestorWeights st b s).get x := by
  induction hperm with
  | nil => rfl
  | cons v _ ih =>
    rename_i l₁ l₂ _
    have h1 := accumulate_cons_get st v l₁ s x
    have h2 := accumulate_cons_get st v l₂ s x
    omega
  | swap u v l =>
    have h1 := accumulate_cons_get st v (u :: l) s x
    have h2 := accumulate_cons_get st u l s x
    have h3 := accumulate_cons_get st u (v :: l) s x
    have h4 := accumulate_cons_get st v l s x
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## The GHOST walk reads weights only through `get` -/

/-- Eligible children agree between extensionally equal weight maps. -/
theorem childrenOf_congr_weights (st : Store) {w w' : Weights}
    (h : Weights.Equiv w w') (minScore : Option Nat) (parent : Root) :
    childrenOf st w minScore parent = childrenOf st w' minScore parent := by
  unfold childrenOf
  congr 1
  apply List.filter_congr
  intro p _
  cases minScore with
  | none => rfl
  | some m => simp only [h p.1]

/-- The child comparison agrees between extensionally equal weight maps. -/
theorem beats_congr_weights {w w' : Weights} (h : Weights.Equiv w w')
    (best cand : Root) : beats w best cand = beats w' best cand := by
  unfold beats
  rw [h best, h cand]

/-- Folding a pick with pointwise-equal comparisons picks the same. -/
private theorem foldl_pick_congr {f g : Root → Root → Bool}
    (h : ∀ a b, f a b = g a b) :
    ∀ (cs : List Root) (a : Root),
      cs.foldl (fun best cand => if f best cand then cand else best) a
        = cs.foldl (fun best cand => if g best cand then cand else best) a
  | [], _ => rfl
  | c :: cs, a => by
    rw [List.foldl_cons, List.foldl_cons, h a c]
    exact foldl_pick_congr h cs _

/-- The winning child agrees between extensionally equal weight maps. -/
theorem maxChild_congr_weights {w w' : Weights} (h : Weights.Equiv w w')
    (cs : List Root) : maxChild w cs = maxChild w' cs := by
  cases cs with
  | nil => rfl
  | cons c t =>
    unfold maxChild
    dsimp only
    rw [foldl_pick_congr (beats_congr_weights h) t c]

/-- The GHOST descent agrees between extensionally equal weight maps:
every step (child enumeration, threshold filter, comparison, tie-break)
reads weights only through `get`. -/
theorem ghostWalk_congr_weights (st : Store) {w w' : Weights}
    (h : Weights.Equiv w w') (minScore : Option Nat) :
    ∀ (fuel : Nat) (head : Root),
      ghostWalk st w minScore fuel head
        = ghostWalk st w' minScore fuel head
  | 0, _ => rfl
  | fuel + 1, head => by
    unfold ghostWalk
    rw [childrenOf_congr_weights st h, maxChild_congr_weights h]
    cases maxChild w' (childrenOf st w' minScore head) with
    | none => rfl
    | some best => exact ghostWalk_congr_weights st h minScore fuel best

/-- #67 (weight-delta layer): head selection depends on the vote tally
only extensionally. A client maintaining the weight map incrementally —
crediting batches in any order (`accumulateAncestorWeights_append`,
`accumulateAncestorWeights_perm`) — selects exactly the head of the
naive spec walk, tie-break included, as long as its maintained map is
`get`-equal to the full tally. -/
theorem computeLmdGhostHead_incremental (st : Store) (startRoot : Root)
    (attestations : List (Nat × AttestationData))
    {anchor : Block} (hanchor : st.getBlock? startRoot = some anchor)
    {w : Weights}
    (hw : Weights.Equiv w
      (accumulateAncestorWeights st attestations anchor.slot))
    (minScore : Option Nat) :
    ghostWalk st w minScore (st.blocks.length + 1) startRoot
      = computeLmdGhostHead st startRoot attestations minScore := by
  unfold computeLmdGhostHead
  rw [hanchor]
  exact ghostWalk_congr_weights st hw minScore (st.blocks.length + 1)
    startRoot

end Store
end LeanSpec.Forks.Lstar
