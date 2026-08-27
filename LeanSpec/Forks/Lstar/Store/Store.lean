/-
Fork-choice store and LMD-GHOST head selection.

Mirrors `src/lean_spec/spec/forks/lstar/containers/store.py` and the
head-selection subset of `src/lean_spec/spec/forks/lstar/fork_choice.py`
in leanSpec (post leanEthereum/leanSpec#1179/#1181):
  - `class Store` — a node's local view of the chain for running fork
    choice, with `AttestationSignatureEntry`.
  - `_checkpoint_is_ancestor(store, ancestor, descendant)`.
  - `_extract_attestations_from_aggregated_payloads(payloads, finalized)`:
    each validator mapped to its latest vote, visited newest-first with
    the equal-slot tie broken toward the larger canonical
    attestation-data root — insertion-order independent since
    leanEthereum/leanSpec#1181.
  - `_accumulate_ancestor_weights(store, attestations, start_slot)` and
    `compute_block_weights(store)`.
  - `_compute_lmd_ghost_head(store, start_root, attestations, min_score)`.
  - `update_head(store)` — the upstream successor of the catalog's
    `compute_head`.
  - `validate_attestation(store, attestation_data)` — availability, slot
    topology, checkpoint-block consistency, ancestry (including the
    descent of the head from the finalized block added by
    leanEthereum/leanSpec#1179 against vote resurrection), head
    observability, and the clock-skew admission horizon.

Divergences from Python, documented per function:
  - Python `dict`s are association lists (`List (key × value)`); dict-key
    uniqueness is a `WellFormed` clause, not a type-level fact.
  - XMSS material is opaque bytes (`SingleMessageAggregate.proof`,
    `AttestationSignatureEntry.signature` — Arklib side), and
    `hash_tree_root` enters only through the `HasHashTreeRoot` typeclass
    (SSZ-7).
  - The unbounded `while` walks (`_checkpoint_is_ancestor`, the weight
    climb, the GHOST descent, the finalized re-derivation) recurse on
    `blocks.length + 1` fuel. On a well-formed store every parent step
    strictly lowers the slot (`WellFormed.parentSlotLt`), so a walk never
    revisits a block and the fuel is never exhausted; Python relies on
    the same invariant for termination.
  - Python `assert`s (internal invariants, not rejections) are modeled as
    total fallbacks: an unknown anchor makes `computeLmdGhostHead` return
    it unchanged (`_compute_lmd_ghost_head`'s `start_root` assert), and a
    missing head state keeps the previous `latest_finalized`
    (`update_head`'s `store.states[new_head]` lookup; the M-4
    blocks-states alignment of leanEthereum/leanSpec#1176).
  - `on_block` is modeled in `Store/OnBlock.lean` (FC-7) and
    `Store/ChainAlignment.lean` (FC-8); `create_store`, `on_gossip_*`,
    `prune_stale_attestation_data`, `accept_new_attestations`, and
    `update_safe_target` are follow-up work.

Proves FC-1 and FC-3 from `docs/lean4-proof-propositions.md`:
  - FC-1: head selection is deterministic — `updateHead` is a pure total
    function of the store (`update_head_deterministic`). Totality is by
    construction (every walk is fuel-bounded), and
    `computeLmdGhostHead_in_store` / `updateHead_head_in_store` give the
    substantive well-definedness: the selected head is the anchor or a
    block the store knows.
  - FC-3: a successfully validated attestation is slot-ordered —
    `source.slot ≤ target.slot ≤ head.slot` (`attestation_topology`,
    from the topology checks of `validateAttestation`).

`Store.WellFormed` states the store invariants extracted in
leanEthereum/leanSpec#1176 (documented and partially enforced upstream by
leanEthereum/leanSpec#1179); FC-2 / FC-4 / FC-6 consume them in
`Store/Ancestry.lean`.
-/

import LeanSpec.Forks.Lstar.Containers.Aggregation
import LeanSpec.Forks.Lstar.Containers.Interval
import LeanSpec.Forks.Lstar.StateTransition
import LeanSpec.SSZ.Hash

namespace LeanSpec.Forks.Lstar

/-- One validator paired with its signature for an attestation
(`AttestationSignatureEntry`); the XMSS signature is opaque bytes. -/
structure AttestationSignatureEntry where
  validatorIndex : ValidatorIndex
  signature : ByteArray
  deriving Inhabited

/-- A node's local view of the chain for running fork choice (`Store`).
Python `dict`s become association lists; see the module docstring. -/
structure Store where
  /-- Current time in intervals since genesis. -/
  time : Interval
  /-- Chain configuration parameters. -/
  config : GenesisConfig
  /-- Root of the head block that fork choice currently selects. -/
  head : Root
  /-- Root of the block a validator is safe to attest to. -/
  safeTarget : Root
  /-- Highest-slot justified checkpoint observed so far; the head walk
  starts here. -/
  latestJustified : Checkpoint
  /-- Finalization as seen from the canonical head — re-derived from the
  head each update, reorg-mutable, never a safety guarantee (upstream
  docstring, leanEthereum/leanSpec#1179). -/
  latestFinalized : Checkpoint
  /-- Known blocks indexed by their root. -/
  blocks : List (Root × Block)
  /-- Post-state of each known block, indexed by block root. -/
  states : List (Root × State)
  /-- Index of the validator that owns this view, or `none` for an
  observer. -/
  validatorIndex : Option ValidatorIndex
  /-- Per-validator signatures observed, grouped by the vote they sign. -/
  attestationSignatures : List (AttestationData × List AttestationSignatureEntry)
  /-- Pending single-message proofs awaiting promotion, grouped by the
  vote they support. -/
  latestNewAggregatedPayloads : List (AttestationData × List SingleMessageAggregate)
  /-- Single-message proofs counted toward fork choice, grouped by the
  vote they support. -/
  latestKnownAggregatedPayloads : List (AttestationData × List SingleMessageAggregate)
  deriving Inhabited

namespace Store

/-- Look up a block by root (`store.blocks[root]`). -/
def getBlock? (st : Store) (r : Root) : Option Block :=
  (st.blocks.find? (fun p => p.1 == r)).map (·.2)

/-- Look up a post-state by block root (`store.states[root]`). -/
def getState? (st : Store) (r : Root) : Option State :=
  (st.states.find? (fun p => p.1 == r)).map (·.2)

/-- A successful block lookup exhibits a stored entry. -/
theorem getBlock?_eq_some_mem {st : Store} {r : Root} {b : Block}
    (h : st.getBlock? r = some b) : (r, b) ∈ st.blocks := by
  unfold getBlock? at h
  cases hf : st.blocks.find? (fun p => p.1 == r) with
  | none => rw [hf] at h; simp at h
  | some entry =>
    rw [hf] at h
    have hb : entry.2 = b := by simpa using h
    have hpred : (entry.1 == r) = true :=
      List.find?_some (p := fun (q : Root × Block) => q.1 == r) hf
    have hr : entry.1 = r := eq_of_beq hpred
    have hmem : entry ∈ st.blocks := List.mem_of_find?_eq_some hf
    rw [← hr, ← hb]
    exact hmem

/-! ## Ancestry (`_checkpoint_is_ancestor`) -/

/-- Climb parent links from `current` toward genesis looking for the
ancestor checkpoint (the loop of `_checkpoint_is_ancestor`): landing on
the ancestor's slot decides by root equality, climbing past it without
landing means the ancestor is off this chain, and leaving the known tree
ends the search. Public so the completeness lemma (FC-6,
`Store/Ancestry.lean`) can reason about each step. -/
def ancestorWalk (st : Store) (ancestor : Checkpoint) :
    Nat → Root → Bool
  | 0, _ => false
  | fuel + 1, current =>
    match st.getBlock? current with
    | none => false
    | some b =>
      if b.slot = ancestor.slot then current == ancestor.root
      else if b.slot < ancestor.slot then false
      else ancestorWalk st ancestor fuel b.parentRoot

/-- Whether `ancestor` lies on `descendant`'s chain of ancestors
(`_checkpoint_is_ancestor`). An ancestor can never sit later in time
than its descendant. -/
def checkpointIsAncestor (st : Store) (ancestor descendant : Checkpoint) :
    Bool :=
  if descendant.slot < ancestor.slot then false
  else ancestorWalk st ancestor (st.blocks.length + 1) descendant.root

/-! ## Attestation validation (`validate_attestation`) -/

/-- Validate an incoming attestation before processing
(`validate_attestation`): the vote must respect the basic laws of time
and topology. Checks, in upstream order — availability of the three
referenced blocks; slot topology (`source ≤ target ≤ head`, the second
check giving `head ≥ source` by transitivity); checkpoint slots matching
the referenced blocks; ancestry along the chain, including the descent
of the head from the finalized block (leanEthereum/leanSpec#1179, so a
stale vote cannot re-enter after pruning drops it); head observability
(a vote cannot predate its head); and the clock-skew admission horizon
(one gossip-disparity interval, in slot units — Python works in `int` to
dodge the `2^64` interval overflow, mirrored here by `Nat`). -/
def validateAttestation (st : Store) (data : AttestationData) :
    ST.Result Unit :=
  let source := data.source
  let target := data.target
  let head := data.head
  -- Availability: a vote counts only if the blocks involved are known.
  match st.getBlock? source.root with
  | none => .error (.unknownSourceBlock source.root)
  | some sourceBlock =>
  match st.getBlock? target.root with
  | none => .error (.unknownTargetBlock target.root)
  | some targetBlock =>
  match st.getBlock? head.root with
  | none => .error (.unknownHeadBlock head.root)
  | some headBlock =>
  -- Topology: history is linear and monotonic, source ≤ target ≤ head.
  if target.slot < source.slot then
    .error (.sourceAfterTarget source.slot target.slot)
  else if head.slot < target.slot then
    .error (.headOlderThanTarget head.slot target.slot)
  -- Consistency: checkpoint slots match the referenced blocks.
  else if sourceBlock.slot ≠ source.slot then
    .error (.sourceSlotMismatch source.slot sourceBlock.slot)
  else if targetBlock.slot ≠ target.slot then
    .error (.targetSlotMismatch target.slot targetBlock.slot)
  else if headBlock.slot ≠ head.slot then
    .error (.headSlotMismatch head.slot headBlock.slot)
  -- Ancestry: fork-choice weight accrues to every ancestor of the head.
  else if !(checkpointIsAncestor st source target) then
    .error .sourceNotAncestorOfTarget
  else if !(checkpointIsAncestor st target head) then
    .error .targetNotAncestorOfHead
  -- Fork choice only ever descends from the finalized block (#1179).
  else if !(checkpointIsAncestor st st.latestFinalized head) then
    .error .headNotDescendantOfFinalized
  -- Head consistency: a vote cannot have observed a head that did not
  -- exist yet.
  else if data.slot < head.slot then
    .error (.attestationSlotBeforeHead data.slot head.slot)
  else
    -- Time: reject votes whose slot has not started, with a one-interval
    -- clock-skew margin, computed in slot units.
    let admissionHorizonInterval := st.time.toNat + GOSSIP_DISPARITY_INTERVALS
    let maxAdmissibleSlot := admissionHorizonInterval / INTERVALS_PER_SLOT
    if maxAdmissibleSlot < data.slot.toNat then
      .error (.attestationTooFarInFuture data.slot.toNat maxAdmissibleSlot)
    else
      .ok ()

/-- FC-3: a successfully validated attestation is slot-ordered — its
source does not exceed its target and its target does not exceed its
head (`head ≥ source` then follows by transitivity). Extracted from the
topology checks of `validateAttestation`. -/
theorem attestation_topology (st : Store) (data : AttestationData)
    (h : validateAttestation st data = .ok ()) :
    data.source.slot ≤ data.target.slot ∧
    data.target.slot ≤ data.head.slot := by
  unfold validateAttestation at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · next hst =>
          split at h
          · simp at h
          · next hth =>
            exact ⟨UInt64.not_lt.mp hst, UInt64.not_lt.mp hth⟩

/-! ## Vote weights -/

/-- Vote weight tallied per block root (Python `dict[Bytes32, int]` with
a default of zero for absent blocks). -/
abbrev Weights := List (Root × Nat)

namespace Weights

/-- Weight recorded for `r`, defaulting to zero. -/
def get (w : Weights) (r : Root) : Nat :=
  ((w.find? (fun p => p.1 == r)).map (·.2)).getD 0

/-- Credit one vote to `r` (`weights[root] += 1`). -/
def bump (w : Weights) (r : Root) : Weights :=
  match w.find? (fun p => p.1 == r) with
  | some p => (r, p.2 + 1) :: w.filter (fun q => !(q.1 == r))
  | none => (r, 1) :: w

end Weights

/-- Descending canonical precedence on votes: newest slot first, an
equal-slot tie toward the larger canonical attestation-data root — the
tie-break rule that makes the LMD view independent of arrival or
insertion order (leanEthereum/leanSpec#1181). -/
def votePrecedence [SSZ.HasHashTreeRoot AttestationData]
    (a b : AttestationData × List SingleMessageAggregate) : Bool :=
  decide (b.1.slot < a.1.slot) ||
  (b.1.slot == a.1.slot &&
    Root.lexLe (SSZ.hashTreeRoot b.1) (SSZ.hashTreeRoot a.1))

/-- Map each participating validator to the latest vote it cast — the
LMD view fork choice runs on
(`_extract_attestations_from_aggregated_payloads`). Votes are visited
newest-first under `votePrecedence`, the first vote seen for a validator
wins, and a vote whose head sits at or below the finalized slot carries
no fork-choice weight. Validator indices are `Nat`, following
`AggregationBits.toValidatorIndices`. -/
def extractAttestationsFromAggregatedPayloads
    [SSZ.HasHashTreeRoot AttestationData]
    (payloads : List (AttestationData × List SingleMessageAggregate))
    (latestFinalizedSlot : Slot) : List (Nat × AttestationData) :=
  (payloads.mergeSort votePrecedence).foldl
    (fun acc vote =>
      -- A vote whose head sits at or below the finalized slot is stale.
      if vote.1.head.slot ≤ latestFinalizedSlot then acc
      else
        vote.2.foldl
          (fun acc proof =>
            (AggregationBits.toValidatorIndices proof.participants).foldl
              (fun acc i =>
                -- Descending order: the first vote seen for a validator
                -- is its winner.
                if acc.any (fun p => p.1 == i) then acc
                else (i, vote.1) :: acc)
              acc)
          acc)
    []

/-- Credit one vote to its head block and every ancestor above
`startSlot` (the climb inside `_accumulate_ancestor_weights`): the walk
stops at the anchor slot or where the chain leaves the known tree.
Public so the incremental-weight lemmas (#67,
`Store/IncrementalWeights.lean`) can reason about each step. -/
def creditChain (st : Store) (startSlot : Slot) :
    Nat → Root → Weights → Weights
  | 0, _, w => w
  | fuel + 1, current, w =>
    match st.getBlock? current with
    | none => w
    | some b =>
      if b.slot ≤ startSlot then w
      else creditChain st startSlot fuel b.parentRoot (w.bump current)

/-- Tally how many latest votes credit each block
(`_accumulate_ancestor_weights`). -/
def accumulateAncestorWeights (st : Store)
    (attestations : List (Nat × AttestationData)) (startSlot : Slot) :
    Weights :=
  attestations.foldl
    (fun w att => creditChain st startSlot (st.blocks.length + 1) att.2.head.root w)
    []

/-- Weigh each block by the latest counted votes landing on it or its
descendants (`compute_block_weights`). -/
def computeBlockWeights [SSZ.HasHashTreeRoot AttestationData] (st : Store) :
    Weights :=
  accumulateAncestorWeights st
    (extractAttestationsFromAggregatedPayloads
      st.latestKnownAggregatedPayloads st.latestFinalized.slot)
    st.latestFinalized.slot

/-! ## LMD-GHOST head selection (`_compute_lmd_ghost_head`) -/

/-- Children of `parent` eligible for the walk: blocks whose parent link
points at it, pruned below `minScore` when a threshold is set (the
`children_map` of `_compute_lmd_ghost_head`). -/
def childrenOf (st : Store) (weights : Weights) (minScore : Option Nat)
    (parent : Root) : List Root :=
  (st.blocks.filter fun p =>
    p.2.parentRoot == parent &&
      match minScore with
      | some m => decide (m ≤ weights.get p.1)
      | none => true).map (·.1)

/-- Whether `cand` beats `best` in the child comparison: strictly
heavier, or equally heavy with a lexicographically larger root. Python's
`max(children, key=lambda c: (weights[c], c))` keeps the first maximum,
so replacement is strict. -/
def beats (weights : Weights) (best cand : Root) : Bool :=
  decide (weights.get best < weights.get cand) ||
  (weights.get best == weights.get cand && !(Root.lexLe cand best))

/-- The winning child: most attestations, ties toward the
lexicographically highest hash. -/
def maxChild (weights : Weights) : List Root → Option Root
  | [] => none
  | c :: cs =>
    some (cs.foldl (fun best cand => if beats weights best cand then cand else best) c)

/-- Greedy descent to the heaviest leaf (the `while` walk of
`_compute_lmd_ghost_head`), on explicit fuel. Public so the descent
lemmas (FC-2, `Store/Ancestry.lean`) can reason about each step. -/
def ghostWalk (st : Store) (weights : Weights)
    (minScore : Option Nat) : Nat → Root → Root
  | 0, head => head
  | fuel + 1, head =>
    match maxChild weights (childrenOf st weights minScore head) with
    | none => head
    | some best => ghostWalk st weights minScore fuel best

/-- Walk the block tree according to the LMD-GHOST rule
(`_compute_lmd_ghost_head`): start from `startRoot`, at each fork take
the heaviest child subtree (ties toward the larger root), stop at a
leaf. The upstream anchor assert (`start_root in store.blocks`) is an
internal invariant, modeled by returning an unknown anchor unchanged. -/
def computeLmdGhostHead (st : Store) (startRoot : Root)
    (attestations : List (Nat × AttestationData))
    (minScore : Option Nat := none) : Root :=
  match st.getBlock? startRoot with
  | none => startRoot
  | some anchor =>
    let weights := accumulateAncestorWeights st attestations anchor.slot
    ghostWalk st weights minScore (st.blocks.length + 1) startRoot

/-! ## Head update (`update_head`) -/

/-- Climb from `current` to its ancestor at `finalizedSlot` (the
finalized re-derivation loop of `update_head`); the walk stops early
when the parent leaves the known tree. Public so the descent lemma
(FC-6, `Store/Ancestry.lean`) can reason about each step. -/
def descendToSlot (st : Store) (finalizedSlot : Slot) :
    Nat → Root → Root
  | 0, current => current
  | fuel + 1, current =>
    match st.getBlock? current with
    | none => current
    | some b =>
      if finalizedSlot < b.slot then
        match st.getBlock? b.parentRoot with
        | none => current
        | some _ => descendToSlot st finalizedSlot fuel b.parentRoot
      else current

/-- Recompute the canonical head and the head-chain finalized checkpoint
(`update_head`, the upstream successor of the catalog's `compute_head`):
reduce the counted pool to each validator's latest vote, descend from
the justified root to the heaviest leaf, then re-derive
`latest_finalized` as the head chain's ancestor at the head state's
finalized slot — keeping the trusted anchor when no block sits at that
slot (fresh checkpoint sync), and keeping the previous checkpoint when
the head state is missing (the M-4 alignment assert upstream). -/
def updateHead [SSZ.HasHashTreeRoot AttestationData] (st : Store) : Store :=
  let latestVotes :=
    extractAttestationsFromAggregatedPayloads
      st.latestKnownAggregatedPayloads st.latestFinalized.slot
  let newHead := computeLmdGhostHead st st.latestJustified.root latestVotes
  let latestFinalized :=
    match st.getState? newHead with
    | none => st.latestFinalized
    | some headState =>
      let finalizedSlot := headState.latestFinalized.slot
      let finalizedRoot :=
        descendToSlot st finalizedSlot (st.blocks.length + 1) newHead
      match st.getBlock? finalizedRoot with
      | none => st.latestFinalized
      | some b =>
        if b.slot = finalizedSlot then
          { root := finalizedRoot, slot := finalizedSlot }
        else st.latestFinalized
  { st with head := newHead, latestFinalized := latestFinalized }

/-! ## Store invariants (leanEthereum/leanSpec#1176 / #1179) -/

/-- The fork-choice store invariants extracted by the formalization in
leanEthereum/leanSpec#1176 and documented / partially enforced upstream
by leanEthereum/leanSpec#1179. `on_block` and the gossip handlers
maintain them; the head-walk theorems assume them.
  - `blocksKeysNodup` / `statesKeysNodup` — Python dict-key uniqueness.
  - `blocksStatesAligned` — every block root has a post-state and vice
    versa (M-4; upstream asserts this at each gossip-path use site).
  - `parentSlotLt` — a known parent sits strictly below its child. The
    STF admits only strictly-future block slots, so block insertion
    preserves it; it bounds every parent walk (and makes the block
    relation acyclic — FC-4's source).
  - `justifiedInBlocks` — the head-walk anchor is a known block
    (`_compute_lmd_ghost_head`'s assert).
  - `justifiedDescendsFromFinalized` — the justified checkpoint sits on
    the finalized chain (M-1). -/
structure WellFormed (st : Store) : Prop where
  blocksKeysNodup : (st.blocks.map (·.1)).Nodup
  statesKeysNodup : (st.states.map (·.1)).Nodup
  blocksStatesAligned :
    ∀ r : Root, (st.getBlock? r).isSome ↔ (st.getState? r).isSome
  parentSlotLt :
    ∀ p ∈ st.blocks, ∀ q ∈ st.blocks,
      q.1 = p.2.parentRoot → q.2.slot < p.2.slot
  justifiedInBlocks : (st.getBlock? st.latestJustified.root).isSome
  justifiedDescendsFromFinalized :
    checkpointIsAncestor st st.latestFinalized st.latestJustified = true

/-! ## FC-1: head selection is deterministic -/

/-- The picked element of the child-comparison fold is the seed or a
list element. -/
private theorem foldl_pick_mem (f : Root → Root → Bool) :
    ∀ (cs : List Root) (a : Root),
      cs.foldl (fun best cand => if f best cand then cand else best) a = a ∨
      cs.foldl (fun best cand => if f best cand then cand else best) a ∈ cs
  | [], _ => .inl rfl
  | c :: cs, a => by
    rw [List.foldl_cons]
    by_cases hf : f a c = true
    · rw [if_pos hf]
      cases foldl_pick_mem f cs c with
      | inl h => rw [h]; exact .inr List.mem_cons_self
      | inr h => exact .inr (List.mem_cons_of_mem c h)
    · rw [if_neg hf]
      cases foldl_pick_mem f cs a with
      | inl h => exact .inl h
      | inr h => exact .inr (List.mem_cons_of_mem c h)

/-- The winning child is one of the candidates. -/
theorem maxChild_mem (weights : Weights) :
    ∀ (cs : List Root) (r : Root), maxChild weights cs = some r → r ∈ cs
  | [], _, h => by simp [maxChild] at h
  | c :: cs, r, h => by
    have hr : cs.foldl
        (fun best cand => if beats weights best cand then cand else best) c
        = r := by
      simpa [maxChild] using h
    cases foldl_pick_mem (beats weights) cs c with
    | inl heq => rw [hr] at heq; rw [← heq]; exact List.mem_cons_self
    | inr hmem => rw [hr] at hmem; exact List.mem_cons_of_mem c hmem

/-- Every eligible child is a block the store knows. -/
theorem childrenOf_mem (st : Store) (weights : Weights)
    (minScore : Option Nat) (parent c : Root)
    (h : c ∈ childrenOf st weights minScore parent) :
    ∃ b, (c, b) ∈ st.blocks := by
  unfold childrenOf at h
  rw [List.mem_map] at h
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p.2, (List.mem_filter.mp hp).1⟩

/-- The GHOST descent returns its start or a stored block: each step
moves to an eligible child, and eligible children are stored blocks. -/
private theorem ghostWalk_in_store (st : Store) (weights : Weights)
    (minScore : Option Nat) :
    ∀ (fuel : Nat) (head : Root),
      ghostWalk st weights minScore fuel head = head ∨
      ∃ b, (ghostWalk st weights minScore fuel head, b) ∈ st.blocks
  | 0, _ => .inl rfl
  | fuel + 1, head => by
    cases hmc : maxChild weights (childrenOf st weights minScore head) with
    | none =>
      left
      simp only [ghostWalk, hmc]
    | some best =>
      have hbest := maxChild_mem weights _ best hmc
      have hstore := childrenOf_mem st weights minScore head best hbest
      right
      simp only [ghostWalk, hmc]
      cases ghostWalk_in_store st weights minScore fuel best with
      | inl heq => rw [heq]; exact hstore
      | inr h => exact h

/-- The selected head is the anchor or a block the store knows — the
well-definedness half of FC-1 (and the membership FC-2 will build on). -/
theorem computeLmdGhostHead_in_store (st : Store) (startRoot : Root)
    (attestations : List (Nat × AttestationData)) (minScore : Option Nat) :
    computeLmdGhostHead st startRoot attestations minScore = startRoot ∨
    ∃ b, (computeLmdGhostHead st startRoot attestations minScore, b)
      ∈ st.blocks := by
  unfold computeLmdGhostHead
  cases hb : st.getBlock? startRoot with
  | none => exact .inl rfl
  | some anchor =>
    exact ghostWalk_in_store st
      (accumulateAncestorWeights st attestations anchor.slot) minScore
      (st.blocks.length + 1) startRoot

/-- FC-1: head selection is deterministic — the same store always yields
the same head. A Lean `def` is pure by construction and every walk is
fuel-bounded, so the theorem records the catalog's meta-property
(upstream renamed `compute_head` to `update_head`); the substantive
well-definedness is `computeLmdGhostHead_in_store` /
`updateHead_head_in_store`. -/
@[simp] theorem update_head_deterministic
    [SSZ.HasHashTreeRoot AttestationData] (st : Store) :
    updateHead st = updateHead st := rfl

/-- On a well-formed store the selected head is always a known block:
the walk starts at the justified anchor, which `WellFormed` places in
the store. -/
theorem updateHead_head_in_store [SSZ.HasHashTreeRoot AttestationData]
    (st : Store) (hwf : WellFormed st) :
    ∃ b, ((updateHead st).head, b) ∈ st.blocks := by
  have hhead : (updateHead st).head =
      computeLmdGhostHead st st.latestJustified.root
        (extractAttestationsFromAggregatedPayloads
          st.latestKnownAggregatedPayloads st.latestFinalized.slot) := rfl
  rw [hhead]
  cases computeLmdGhostHead_in_store st st.latestJustified.root
      (extractAttestationsFromAggregatedPayloads
        st.latestKnownAggregatedPayloads st.latestFinalized.slot) none with
  | inl heq =>
    rw [heq]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hwf.justifiedInBlocks
    exact ⟨b, getBlock?_eq_some_mem hb⟩
  | inr h => exact h

end Store
end LeanSpec.Forks.Lstar
