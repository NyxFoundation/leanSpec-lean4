---
title: Spec Feedback Derived from the Lean 4 Proofs
last_updated: 2026-07-25
tags:
  - formal-verification
  - safety
  - consensus
  - fork-choice
  - ssz
  - feedback
---

# Spec Feedback Derived from the Lean 4 Proofs

## Purpose

leanSpec is the **reference specification** for the Lean Ethereum consensus layer.
It is not a production node — its performance does not matter. What matters is that
every client team transliterates it into their own implementation. Any ambiguity,
implicit precondition, or non-determinism in the reference becomes a *class* of bugs
replicated across all clients, surfacing only in cross-client interop.

This document reports what the Lean 4 formalization in this repository
(`LeanSpec/`) surfaced about the upstream Python spec
([leanEthereum/leanSpec](https://github.com/leanEthereum/leanSpec), reviewed at
HEAD `43246bd6`, 2026-06-26). It has two roles:

1. **Assurances** — which parts of the spec are formally verified, so client teams
   can use the theorems as conformance targets.
2. **Feedback** — where the proofs revealed missing preconditions, non-determinism,
   or under-specification that clients would each resolve differently.

Findings are ranked by their impact *as a reference spec* (how badly they propagate
to clients), not by Python runtime cost. Performance observations are deliberately
excluded — clients optimize with their own data structures.

## How to read severity

- **Critical** — a divergence or missing rule that would let two conforming clients
  reach different consensus state, or a DoS surface every client inherits silently.
- **High** — under-specification that different languages/teams will resolve
  incompatibly, or a wire-format edge that is fail-closed only by accident in Python.
- **Medium** — an unstated invariant the proofs had to assume; safe today but
  load-bearing and undocumented.

---

## Part 1 — Assurances (formally verified, usable as conformance targets)

The following propositions from [`lean4-proof-propositions.md`](./lean4-proof-propositions.md)
are proved as Lean theorems that type-check under `lake build`. Client teams can treat
each as a property their own implementation must satisfy.

### State transition (`state_transition.py`)

- **ST-1** — `process_slots` always reaches `state.slot == target_slot` for
  `slot ≤ target`.
- **ST-2** — after `process_block_header`, `latest_block_header.slot == block.slot`,
  and it survives the full transition.
- **ST-3** — both `latest_justified.slot` and `latest_finalized.slot` are
  **monotonically non-decreasing** across any successful transition (no checkpoint
  regression).
- **ST-4** — every phase preserves `latest_finalized.slot ≤ latest_justified.slot`
  (finalized never overtakes justified).
- **ST-5** — the transition is a **pure deterministic function** of `(state, block)`
  — same inputs, same output — *modulo* the omitted `hash_tree_root` calls (see
  Coverage limits below).
- **ST-6** — finalization is **irreversible**.

### Validator (`identifiers.py`)

- **VAL-1 / VAL-3** — proposer selection is round-robin (`slot % num_validators`) and
  each slot has **exactly one** proposer.

### Containers (`checkpoint.py`, `slot.py`)

- **CONT-1** — checkpoint ordering is determined by slot.
- **CONT-2** — a slot is justifiable after a distance iff that distance is within the
  window (≤ 5), a perfect square, or pronic. The Lean characterization matched the
  Python predicate exactly, including after the `ae4adf15` refactor.

### SSZ & primitives (`spec/ssz/*.py`, `crypto/merkleization.py`)

- **SSZ-1/2/3/4/5** — `decode ∘ encode = id` (round-trip) plus the length/range
  invariants for `Boolean`, `Uint64`, `Bytes32`, `Vector`.
- **SSZ-6** — `_next_pow2` minimality for `x > 0`.
- **SSZ-7** — `hash_tree_root` collision resistance is modeled as an `axiom`
  (delegated to Arklib); it is a per-type assumption, not a cross-type claim.

The #941/#945 (bitfield padding) and #779 (container offset-gap) fixes are all
reflected — the current Python matches what these proofs model.

### Coverage limits (be honest with client teams)

The proofs are about **result values** and deliberately omit:

- All `hash_tree_root` calls — so the parent-root check, body-root, and post-state
  STATE_ROOT_MISMATCH check are *assumed*, not modeled.
- **Loop step-count / termination-as-cost** — Lean's `termination_by` proves the
  loop ends, which is silent about it being an unbounded real loop (see Critical-1).
- Only the `decode ∘ encode = id` direction — `encode ∘ decode = id` (injectivity:
  no two byte strings decode to one value) is **unproved** for every type. Findings
  High-3 lives exactly in this gap.
- No Lean model for the offset-table machinery of `List`/`Vector`/`Container` or for
  bitfields — again where the SSZ wire-format findings live.
- The **entire Fork Choice domain (FC-\*) is unproved** — Critical-2 and the
  Medium fork-choice items below are *suspected* from reading the Python, not verified.

---

## Part 2 — Feedback (ranked by impact as a reference spec)

### Critical-1 — Block acceptance has no future-slot horizon in the spec

**Where:** `on_block` (`fork_choice.py:533-596`) → `state_transition`
(`state_transition.py:378`) → `process_slots` (`state_transition.py:71-76`).

`process_slots` only rejects `target_slot ≤ state.slot`; there is no upper bound. The
`max_admissible_slot` horizon (`fork_choice.py:297`) guards **attestations only**, not
blocks. Because the proposer for a slot is `slot % num_validators`, a single honest-key
holder is the valid proposer for infinitely many slots and can produce a validly-signed
block at, e.g., `slot = 2^63`; the `while state.slot < target_slot` loop then iterates
`block.slot - state.slot` times.

**Why the proof surfaced it:** `processSlots` (`StateTransition.lean`) is total with
`termination_by target.toNat - s.slot.toNat`. The proof shows the loop *terminates
mathematically* — which is exactly silent about it being an unbounded real loop. ST-1
constrains the *result*, never the *step count*.

**Reference-spec impact:** the future-slot horizon for blocks is not written in the
spec, so every client reads "not written ⇒ not required" and inherits the same DoS
surface. This must be a stated precondition of block acceptance.

**Suggested spec change:** `on_block` / `state_transition` should reject a block whose
slot exceeds the current-time slot horizon *before* calling `process_slots`, mirroring
the attestation horizon at `fork_choice.py:297`.

### Critical-2 — Head is not a pure function of store contents (equivocation tie-break is insertion-order dependent)

**Where:** `_extract_attestations_from_aggregated_payloads`
(`fork_choice.py:661-677`), self-admitted in the comment at `:649`.

For a validator with two *distinct* `AttestationData` at the **same slot**
(equivocation), the code keeps whichever data was **first inserted into the dict** —
i.e. arrival order, not store content. Two honest nodes holding the identical set of
blocks and aggregates, received in different orders, can assign the equivocator's
weight to different branches and select **different heads persistently**.

**Reference-spec impact:** this is the worst class of reference bug. Client teams will
each resolve the tie differently — arrival order, `hash_tree_root` order, validator
index order — every unit test passes, and heads diverge only on the interop network.
The Fork Choice domain is not yet formalized here, but this makes the intended
**FC-1 (head determinism) proposition false** for any store modeled as a finite map.

**Suggested spec change:** specify a deterministic tie-break as part of the spec (e.g.
keep the data with the lexicographically-highest `hash_tree_root`, or discard
equivocating validators entirely). This closes what the `b15da086` / `81ed4aa3` /
`3bd2cd58` fix series circled without resolving.

### High-1 — `assert` vs. rejection is not distinguishable at the type level

**Where:** `SpecRejectionError` subclasses `AssertionError` (`errors.py:108-113`);
bare `assert`s reachable from network input at `state_transition.py:225, 312, 338` and
`fork_choice.py:364, 474, 770`.

Because protocol rejection and programmer-error assertion share one exception type, a
client cannot tell from the spec whether a given `assert` is:

- a **protocol rejection** every client must reproduce, or
- an **internal invariant** that provably cannot fire.

Different languages then diverge: some `panic`, some throw, and `python -O` strips bare
asserts entirely while leaving the typed rejections.

**Why the proof helps:** the formalization already classifies these. For example
`state_transition.py:312` (`assert justified_index is not None`) *provably holds* — the
target passed the not-justified filter, so `target.slot > finalized` — matching Lean's
`justifiedIndexAfter` branch. Whereas `state_transition.py:338` (root-in-`root_to_slot`
membership) is the one the Lean model deliberately diverges on: `applyJustification`
(`StateTransition.lean:281-284`) **drops** a tally whose root has no slot instead of
asserting. That split is the exact classification the spec should encode.

**Suggested spec change (continues the #871 direction):** make `SpecRejectionError`
subclass `Exception`, and reclassify each remaining bare `assert` as either a typed
`RejectionReason` or a documented, provably-unreachable internal invariant. This repo's
proofs can supply the "provably unreachable" evidence.

### High-2 — Partial functions enforce preconditions by `raise`

**Where:** `is_justifiable_after` (`slot.py:50`, assert-enforced precondition),
`proposer_for_slot` (`identifiers.py:26-33`, raises on empty registry),
`process_attestations` (`state_transition.py:229-236`, `batched(data, validator_count)`
crashes if `validator_count == 0`, and `zip(..., strict=True)` crashes on a
length-mismatched deserialized state).

Each is a partial function whose precondition is guarded by callers rather than by the
function. In the full block flow these preconditions hold, but the functions are public
and reachable directly or on a state reconstructed from untrusted bytes (sync/DB).

**Why the proof surfaced it:** these are precisely the spots where the Lean proofs
needed a **side hypothesis** (e.g. VAL-1/VAL-3 excluded the empty registry by
assumption; `is_justifiable_after`'s precondition is the non-local implication that
made CONT-2 need a side condition). A precondition the prover has to state explicitly
is a precondition a client will drop implicitly.

**Suggested spec change:** make these total — return `Option`/`False`, or raise a typed
domain rejection — so the behavior is defined regardless of the transliterating
language's type system. Concretely: `is_justifiable_after` returns `False` for
`self < finalized_slot`; `proposer_for_slot` returns a typed rejection (or state a
genesis-checked "validators non-empty" invariant on `State`); `process_attestations`
validates `len(justifications_validators)` is a multiple of `validator_count` and
rejects an empty registry before `batched`.

### High-3 — SSZ variable-length list decoder accepts `first_offset == 0`

**Where:** `collections.py:601-617`.

The decoder checks `first_offset > scope` and `first_offset % 4`, but not
`first_offset == 0`. With `first_offset = 0`, `num_elements` computes as 0, yet the
boundary list becomes `[0, scope]`, so the decoder tries to parse **one** element
spanning the whole scope while believing the count is zero. Reproduced:
`List[ByteList].decode_bytes(bytes.fromhex("00000000aabbccdd"))` fails — but with an
error from the wrong layer for the wrong reason.

**Reference-spec impact:** SSZ is the **wire format that must agree byte-for-byte
across clients**. Today this is fail-closed only *by accident* — every element decoder
enforces exact reads, so the stolen offset bytes eventually cause a short-read. That is
correctness by accident, not by construction; a transliteration into a language with a
more permissive element decoder can produce parser confusion or over-allocation. This
sits in the unproved `encode ∘ decode = id` (injectivity) direction (see Coverage
limits).

**Suggested spec change:** `SSZList.deserialize` should reject
`first_offset == 0` (equivalently `first_offset < BYTES_PER_LENGTH_OFFSET`) before
building the boundary list.

### Medium — Fork-choice invariants maintained only by convention

These are unstated invariants the Fork Choice domain (not yet formalized) relies on. A
Lean `Store.WellFormed` model would have to assume each; documenting them in the spec
turns a hidden assumption into a client-checkable rule.

- **No link between `latest_justified` and the finalized chain.** `advance_to` is
  slot-only (`checkpoint.py:23-30`); nothing checks `latest_justified.root` descends
  from `latest_finalized.root`. Suggested: assert/check
  `_checkpoint_is_ancestor(latest_finalized, latest_justified)` after each update, or
  document the byzantine precondition.
- **Admission predicate ≠ prune predicate (votes can resurrect).** `b15da086` prunes
  votes by slot *and* ancestry (`fork_choice.py:169-173`), but `validate_attestation`
  (`:195-302`) checks neither against `latest_finalized`, and the weight-side filter
  (`:666`) checks slot only. A re-gossiped stale aggregate re-enters the pool. Harmless
  to the head today, but it breaks any "pruning is a fixpoint" lemma and is a
  pool-inflation vector. Suggested: `validate_attestation` should reject attestations
  whose head does not descend from `latest_finalized`, mirroring the prune predicate.
- **Pruning against a reorg-mutable `latest_finalized` is irreversible.**
  `store.py:46-51` documents `latest_finalized` as reorg-mutable (can retreat), but
  `prune_stale_attestation_data` permanently deletes votes based on a value that may
  later retreat. After a retreat, a node that pruned and one that did not hold
  different vote sets → different heads. A store-level finalized-monotonicity theorem
  (the FC analog of ST-4) is therefore **false** as written. Suggested: make store
  finalization monotone, or defer pruning to an irreversibility depth.
- **Gossip-path asserts depend on the `blocks.keys() == states.keys()` invariant**
  (`fork_choice.py:364, 474, 770`). Same issue as High-1, on the fork-choice side; the
  invariant should be stated and checked at store construction.

---

## Traceability

- Upstream reviewed: `leanEthereum/leanSpec` HEAD `43246bd6` (2026-06-26).
- Proof catalog: [`lean4-proof-propositions.md`](./lean4-proof-propositions.md).
- Proof sources: `LeanSpec/Forks/Lstar/StateTransition.lean`, `Slot.lean`,
  `Containers/{Checkpoint,State,Identifiers}.lean`, `LeanSpec/SSZ/*.lean`.
- Note: the four SSZ Lean files previously cited the pre-#790 paths
  `src/lean_spec/types/*.py`; they now cite the current
  `src/lean_spec/spec/ssz/*.py` (`boolean.py`, `uint.py`, `byte_arrays.py`,
  `collections.py`). This was a citation-only drift with zero semantic impact.
