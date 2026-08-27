---
title: leanSpec → Lean4 Theorem Proving Proposition Catalog
last_updated: 2026-07-25
tags:
  - lean4
  - formal-verification
  - propositions
  - safety
  - consensus
  - checklist
---

# leanSpec → Lean4 Theorem Proving Proposition Catalog

## Context

leanSpec is the Python specification for the Lean Ethereum consensus layer.
To guarantee the safety of client implementations, we extract **propositions** that should hold at the spec level and prove them as theorems in Lean 4.

- **Goal**: Design a safe client specification.
- **Approach**: Start from per-function input/output propositions, then expand to cross-cutting invariants.
- **Role of this document**: A catalog of the propositions to be formalized in Lean 4, presented as a checklist.
    - Each proposition is a checkbox item (`[x]` proved, `[ ]` open, `[axiom]` modeled as a cryptographic assumption).
    - Heading text is itself a predicate-form statement; the body is anchored by a Lean 4 sample snippet.
    - Organized **by domain** (1:1 with the Lean 4 directory layout).
    - Eight domains: SSZ & primitive types / Containers / State Transition / Fork Choice / Validator / Networking / Storage / Sync.
    - **Out of scope**: The algebraic properties of cryptographic primitives, the KoalaBear field, and the XMSS signature scheme are handled on the **Arklib** side. This document only covers the call sites (e.g. SSZ-7 modeled as an `axiom`, VAL-5 key-preparation state management).

## Approach

### Items per proposition

The proposition statement itself is given by the checklist item text in predicate form. Each proposition block is composed of the items below (in the order they appear). `Source` and `Note` are optional; the Lean sample is in principle required.

- **Source**: The leanSpec (Python) function or type name that backs the proposition (e.g. `process_slots`, `Uint64.encode`, `Database.batch_write`). This makes it traceable as "which behavior of the Python spec does this proposition extract?". For cross-cutting properties that cannot be localized to a single function, give the main function plus an annotation (e.g. `state_transition` (global invariant under arbitrary repeated application)).
- **Note**: A one-line natural-language description of the role of the function the `Source` points to. Some function names alone do not convey what they do (e.g. `is_justifiable_after` does not by itself tell you what is being judged), so a note is added. Omitted for self-explanatory functions like `encode` / `decode`.
- **Sample code**: A Lean 4 stub of the proposition. The proof body is left as `sorry`:

  ```lean
  -- Lean 4 stub of the proposition. Proof body deferred to `sorry`.
  theorem foo (s : State) : P s := by sorry
  ```

  The real code is expected to depend on `Std`, `Mathlib`, or a custom `LeanSpec.Prelude`. Types like SSZ / State / Block are defined separately in their own files (`LeanSpec.Containers.*`).

### Proposition ID convention

Format: `<DOMAIN>-<number>`. `DOMAIN` is the abbreviation of the owning area:

| Prefix | Domain | Lean 4 location |
|---|---|---|
| `SSZ` | SSZ & primitive types | `LeanSpec/Types`, `LeanSpec/SSZ` |
| `CONT` | Containers (Checkpoint, Slot algebra, etc.) | `LeanSpec/Containers` |
| `ST` | State transition | `LeanSpec/Forks/Lstar/State` |
| `FC` | Fork choice | `LeanSpec/Forks/Lstar/Store` |
| `VAL` | Validator duties | `LeanSpec/Validator` |
| `NET` | Networking (req/resp) | `LeanSpec/Networking` |
| `STOR` | Storage | `LeanSpec/Storage` |
| `SYNC` | Sync FSM | `LeanSpec/Sync` |

### Checkbox legend

- `[x]` — proved in Lean 4 (file path / theorem name cited in the entry).
- `[ ]` — open; sample code stubbed with `sorry`.
- `[axiom]` — out-of-scope for proof; modeled as a cryptographic assumption (`axiom`).

## Progress summary

| Domain | Proved | Open | Axiom | Total |
|---|---:|---:|---:|---:|
| SSZ | 6 | 0 | 1 | 7 |
| CONT | 2 | 0 | 0 | 2 |
| ST | 7 | 0 | 0 | 7 |
| FC | 8 | 0 | 0 | 8 |
| VAL | 5 | 0 | 0 | 5 |
| NET | 2 | 0 | 0 | 2 |
| STOR | 2 | 0 | 0 | 2 |
| SYNC | 2 | 0 | 0 | 2 |
| **Total** | **34** | **0** | **1** | **35** |

## SSZ & primitive types

**SSZ (Simple Serialize)** is the deterministic serialization format used in the Ethereum consensus layer. Every value is uniquely represented in two ways: (1) a byte-string `encode`, and (2) a 32-byte commitment `hash_tree_root` obtained by Merkleization. The primitive types are `Boolean`, `Uint{8,16,32,64}`, fixed-length `Bytes32`, variable-length `List`, fixed-length `Vector`, and bit sequences `Bitlist` / `Bitvector`.

The propositions here guarantee the **mathematical soundness of the encoder**: round-trip (`decode ∘ encode = id`), length invariants (fixed-length types always encode to N bytes), range constraints (`Uint64` values lie in `[0, 2^64)`), and so on. If these break, every upper layer (Container, `hash_tree_root`, fork-choice inputs) becomes untrustworthy. Implementations live in `LeanSpec/Types/*` and `LeanSpec/SSZ/*`.

- [x] **SSZ-1: A Boolean is recovered by encode/decode**
  - Source: `Boolean.encode` / `Boolean.decode`
  - Proved at: `LeanSpec/SSZ/Boolean.lean` (`Boolean.decode_encode`)
  - Sample code:

    ```lean
    theorem boolean_roundtrip (b : Boolean) :
        Boolean.decode (Boolean.encode b) = some b := by sorry
    ```

- [x] **SSZ-2: A Uint64 value lies in [0, 2^64)**
  - Source: `Uint64` (type definition)
  - Proved at: `LeanSpec/SSZ/Uint64.lean` (`Uint64.range`)
  - Sample code:

    ```lean
    theorem uint64_range (v : Uint64) :
        v.toNat < 2 ^ 64 := by sorry
    ```

- [x] **SSZ-3: A Uint64 is recovered by 8-byte LE encode/decode**
  - Source: `Uint64.encode` / `Uint64.decode`
  - Proved at: `LeanSpec/SSZ/Uint64.lean` (`Uint64.decode_encode`, `Uint64.encode_size`)
  - Sample code:

    ```lean
    theorem uint64_roundtrip (v : Uint64) :
        Uint64.decode (Uint64.encode v) = some v := by sorry
    -- ✅ proved in LeanSpec/SSZ/Uint64.lean as `Uint64.decode_encode`

    theorem uint64_encode_length (v : Uint64) :
        (Uint64.encode v).size = 8 := by sorry
    -- ✅ proved in LeanSpec/SSZ/Uint64.lean as `Uint64.encode_size`
    ```

- [x] **SSZ-4: Bytes32 is always 32 bytes**
  - Source: `Bytes32` (type definition)
  - Proved at: `LeanSpec/SSZ/Bytes32.lean` (`Bytes32.size_eq_32`)
  - Sample code:

    ```lean
    theorem bytes32_length (bs : Bytes32) : bs.size = 32 := bs.property
    ```

- [x] **SSZ-5: SSZVector length equals the type parameter n**
  - Source: `SSZVector` (type definition)
  - Proved at: `LeanSpec/SSZ/Vector.lean` (`SSZVector.sszvector_length`)
  - Sample code (`.length` reconciled to Lean's `Array.size`; the two coincide for `Array T`):

    ```lean
    theorem sszvector_length {T : Type} {n : Nat} (v : SSZVector T n) :
        v.data.size = n := v.size_eq
    -- ✅ proved in LeanSpec/SSZ/Vector.lean as `SSZVector.sszvector_length`
    ```

- [x] **SSZ-6: Rounding up to a power of two yields the smallest such value ≥ the input**
  - Source: `get_power_of_two_ceil` (renamed `_next_pow2` in current leanSpec, `src/lean_spec/spec/crypto/merkleization.py`)
  - Note: Returns the smallest power of two that is at least `x` (used in Merkle-tree padding to make leaf counts powers of two).
  - Proved at: `LeanSpec/SSZ/Utils.lean` (`ceil_pow2_minimal`)
  - Sample code (`ceilPow2` realized as `getPowerOfTwoCeil`, mirroring the Python name):

    ```lean
    theorem ceil_pow2_minimal (x : Nat) (h : 0 < x) :
        x ≤ ceilPow2 x ∧ ∃ k, ceilPow2 x = 2 ^ k ∧
          (k = 0 ∨ 2 ^ (k - 1) < x) := by sorry
    -- ✅ proved in LeanSpec/SSZ/Utils.lean as `ceil_pow2_minimal`
    ```

- [axiom] **SSZ-7: Distinct values produce distinct hash-tree roots (collision resistance)**
  - Source: `hash_tree_root` (`src/lean_spec/spec/crypto/merkleization.py`)
  - Declared at: `LeanSpec/SSZ/Hash.lean` (`HashTreeRoot.collisionResistance`)
  - Sample code:

    ```lean
    axiom HashTreeRoot.collisionResistance :
        ∀ x y, hashTreeRoot x = hashTreeRoot y → x = y
    -- Note: not a strict theorem; used as a cryptographic assumption.
    -- ✅ declared in LeanSpec/SSZ/Hash.lean as `HashTreeRoot.collisionResistance`
    ```

## Containers

A **Container** is a composite SSZ type — a struct with named fields (analogous to a Solidity `struct`). All **on-chain / on-wire data structures** in the consensus layer are defined as Containers: `Checkpoint` (a root + slot pointer into the chain), `BlockHeader`, `AttestationData`, `Attestation`, `AggregatedAttestation`, etc.

`Checkpoint` in particular is the core of the finality machinery — fork choice decides the head based on "which checkpoint is justified / finalized" — so the **total order** between Checkpoints, and whether a target is at a **justifiable distance** from a given finalized checkpoint (the disjunction `δ ≤ 5`, `δ = k²`, `δ = k(k+1)`), are natural targets for propositions. Implementations live in `LeanSpec/Containers/*`.

- [x] **CONT-1: Checkpoint ordering is determined by slot**
  - Source: `Checkpoint` (comparison operator; upstream has no explicit `__lt__` — the order in use is the slot comparison inside `advance_to`, `src/lean_spec/spec/forks/lstar/containers/checkpoint.py`)
  - Proved at: `LeanSpec/Forks/Lstar/Containers/Checkpoint.lean` (`Checkpoint.checkpoint_lt_iff_slot_lt`; `advanceTo_eq_ite` connects the order to `advance_to`)
  - Sample code:

    ```lean
    theorem checkpoint_lt_iff_slot_lt (c1 c2 : Checkpoint) :
        c1 < c2 ↔ c1.slot < c2.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Containers/Checkpoint.lean as
    --    `Checkpoint.checkpoint_lt_iff_slot_lt`
    ```

- [x] **CONT-2: justifiable holds iff the slot distance is one of three forms**
  - Source: `is_justifiable_after` (`src/lean_spec/spec/forks/lstar/slot.py`)
  - Note: Decides whether the target slot is at a justifiable distance from the finalized-checkpoint slot (LMD-CASPER justification-candidate check). Total since leanEthereum/leanSpec#1178: a slot before the finalized boundary returns `False` (previously an `assert` crash); the guard is proved as `Slot.justifiable_before_finalized`.
  - Proved at: `LeanSpec/Forks/Lstar/Slot.lean` (`Slot.justifiable_iff`, via correctness of the hand-rolled `isqrt`: `isqrt_le` / `isqrt_lt_succ` / `isqrt_eq`; the settled-slot guard as `Slot.justifiable_before_finalized`)
  - Sample code:

    ```lean
    theorem justifiable_iff
        (finalized target : Slot) (h : finalized ≤ target) :
        Slot.isJustifiableAfter finalized target ↔
          let δ := target.toNat - finalized.toNat
          δ ≤ 5 ∨ (∃ k, δ = k * k) ∨ (∃ k, δ = k * (k + 1)) := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Slot.lean as `Slot.justifiable_iff`
    ```

## State Transition

The **State Transition Function (STF)** is the pure function that computes the next `BeaconState` from the current `BeaconState` plus an input `Block`; it is the heart of consensus. It is expressed as the composition of `process_slots` (an empty transition that advances slots) and `process_block` (block application).

The propositions here guarantee that **the STF advances state as expected**: after `process_slots`, `state.slot` reaches the target; after `process_block_header`, `latest_block_header.slot` matches the block's slot; the justified/finalized slots are monotonically non-decreasing across transitions; `justified.slot ≥ finalized.slot` always holds; and ultimately **finalization is irreversible** (we never roll back to a slot earlier than an already-finalized checkpoint). If these break, defenses against forking attacks and reorgs collapse. Implementations live in `LeanSpec/Forks/Lstar/State/*`.

- [x] **ST-1: Empty-slot advancement makes state.slot equal target**
  - Source: `process_slots` (`src/lean_spec/spec/forks/lstar/state_transition.py`)
  - Note: Repeatedly advances state up to the target slot empty (no blocks).
  - Proved at: `LeanSpec/Forks/Lstar/StateTransition.lean` (`State.process_slots_advances`)
  - Sample code:

    ```lean
    theorem process_slots_advances (s : State) (target : Slot)
        (h : s.slot ≤ target) :
        (State.processSlots s target).slot = target := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/StateTransition.lean as `State.process_slots_advances`
    ```

- [x] **ST-2: After applying a block header, latest-header slot equals block slot**
  - Source: `process_block_header` (`src/lean_spec/spec/forks/lstar/state_transition.py`)
  - Note: Applies the header part of a block to the state and updates `latest_block_header`.
  - Proved at: `LeanSpec/Forks/Lstar/StateTransition.lean` (`State.process_block_header_slot`)
  - Sample code:

    ```lean
    theorem process_block_header_slot
        (s : State) (b : Block) (s' : State)
        (h : State.processBlockHeader s b = .ok s') :
        s'.latestBlockHeader.slot = b.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/StateTransition.lean as `State.process_block_header_slot`
    ```

- [x] **ST-3: Checkpoint slots are monotonically non-decreasing across transitions**
  - Source: `state_transition` (the `process_*` family in general; `src/lean_spec/spec/forks/lstar/state_transition.py`)
  - Note: Composition of `process_slots` and `process_block`. One-block state transition.
  - Proved at: `LeanSpec/Forks/Lstar/StateTransition.lean` (`State.checkpoint_monotone`)
  - Sample code (the proved statement adds an `AnchorWF s` hypothesis — `latestBlockHeader.slot = 0 → latestJustified.slot = 0 ∧ latestFinalized.slot = 0` — because the first block's genesis anchoring force-assigns slot-0 checkpoints, making the bare statement false for adversarial states; `AnchorWF` holds for every state reachable from genesis, ST-4):

    ```lean
    theorem checkpoint_monotone
        (s s' : State) (b : Block)
        (h : State.transition s b = .ok s') :
        s.latestJustified.slot ≤ s'.latestJustified.slot ∧
        s.latestFinalized.slot ≤ s'.latestFinalized.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/StateTransition.lean as `State.checkpoint_monotone`
    --    (with the additional hypothesis `hwf : AnchorWF s`)
    ```

- [x] **ST-4: The justified slot is always at least the finalized slot**
  - Source: `process_justification_and_finalization` (and related `process_*`; a reachable-state invariant maintained by multiple functions — realized as `process_attestations` in current leanSpec)
  - Proved at: `LeanSpec/Forks/Lstar/Reachable.lean` (`justified_ge_finalized`, by induction on `Reachable`; per-phase preservation lemmas in `LeanSpec/Forks/Lstar/StateTransition.lean`)
  - Sample code:

    ```lean
    theorem justified_ge_finalized (s : State) (hreach : Reachable s) :
        s.latestJustified.slot ≥ s.latestFinalized.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Reachable.lean as `justified_ge_finalized`
    --    (Reachable also discharges the AnchorWF hypothesis of ST-3 / ST-6:
    --     see `checkpoint_monotone_of_reachable` / `finalization_irreversible_of_reachable`)
    ```

- [x] **ST-5: The state transition function is pure**
  - Source: `state_transition` (a meta-property of the entire signature; `src/lean_spec/spec/forks/lstar/state_transition.py`)
  - Note: The same STF as ST-3. Identical inputs always yield identical outputs.
  - Proved at: `LeanSpec/Forks/Lstar/StateTransition.lean` (`State.state_transition_pure`)
  - Sample code: written as a `@[simp]` lemma.

    ```lean
    @[simp] theorem state_transition_pure (s : State) (b : Block) :
        State.transition s b = State.transition s b := rfl
    -- ✅ proved in LeanSpec/Forks/Lstar/StateTransition.lean as `State.state_transition_pure`
    ```

- [x] **ST-6: Finalization is irreversible**
  - Source: `state_transition` (global invariant under arbitrary repeated application)
  - Note: The same STF as ST-3.
  - Proved at: `LeanSpec/Forks/Lstar/StateTransition.lean` (`State.finalization_irreversible`, the `latestFinalized` half of ST-3)
  - Sample code (same `AnchorWF s` hypothesis as ST-3):

    ```lean
    theorem finalization_irreversible
        (s s' : State) (b : Block)
        (h : State.transition s b = .ok s') :
        s.latestFinalized.slot ≤ s'.latestFinalized.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/StateTransition.lean as
    --    `State.finalization_irreversible` (with `hwf : AnchorWF s`)
    ```

- [x] **ST-7: Checkpoint replacement is strictly forward (no same-slot root swap)**
  - Source: `process_attestations` / `process_block_header` (the `Checkpoint.advance_to` strict slot comparison and the `finalized < source.slot` finalization guard; `src/lean_spec/spec/forks/lstar/state_transition.py`)
  - Note: ST-3/ST-6 bound only the checkpoint **slots** — they would still admit a transition that swaps `latest_justified` / `latest_finalized` to a different root at the same slot. This proposition closes that gap at the STF level: a successful transition either leaves each checkpoint unchanged **as a whole value (root included)** or replaces it with one at a strictly higher slot. The one designed exception is genesis anchoring (the first block force-assigns both checkpoints to its parent root at slot 0, filling in the genesis root), excluded by the `latestBlockHeader.slot ≠ 0` hypothesis. Cross-branch root *ancestry* is deliberately not an STF property — upstream leanEthereum/leanSpec#1179 documents on `Checkpoint.advance_to` that "selection is by slot only" and on `Store.latest_finalized` that the ancestry is a separate store invariant (future FC work).
  - Proved at: `LeanSpec/Forks/Lstar/CheckpointForward.lean` (`State.checkpoint_forward`; per-phase lemmas `applyJustification_forward`, `processAttestation_forward`, `processAttestations_forward`, and `processBlockHeader_checkpoints_of_ne_zero`)
  - Sample code:

    ```lean
    theorem checkpoint_forward
        (s s' : State) (b : Block)
        (hnz : s.latestBlockHeader.slot ≠ 0)
        (h : State.transition s b = .ok s') :
        (s'.latestJustified = s.latestJustified ∨
          s.latestJustified.slot < s'.latestJustified.slot) ∧
        (s'.latestFinalized = s.latestFinalized ∨
          s.latestFinalized.slot < s'.latestFinalized.slot) := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/CheckpointForward.lean as
    --    `State.checkpoint_forward`
    ```

## Fork Choice

**Fork choice** is the algorithm that decides which branch is the canonical chain when multiple valid block candidates exist. Lean Ethereum (lstar) is **LMD-GHOST**-based: it tallies the weight of the latest attestations and selects the heaviest branch downstream of the justified checkpoint as the head. The `Store` is the state holding fork-choice inputs — the block set, the attestation cache, and the latest justified/finalized checkpoints.

The propositions here guarantee **fork-choice consistency**: `compute_head` is deterministic for the same Store; the chosen head is always a descendant of `latest_justified`; the topological constraint `source.slot ≤ target.slot ≤ head.slot` on attestations; the block-relation graph is acyclic (no cycles in the `parent_root` chain); and the block-production loop terminates in finitely many steps. If these break, the head becomes ill-defined and the network splits. Implementations live in `LeanSpec/Forks/Lstar/Store/*`. The store invariants these proofs assume are the ones extracted in leanEthereum/leanSpec#1176 (documented and partially enforced upstream by #1179), stated as `Store.WellFormed`.

- [x] **FC-1: Head selection is deterministic (a pure function)**
  - Source: `compute_head` (renamed upstream: `update_head`, driving `_compute_lmd_ghost_head`, `src/lean_spec/spec/forks/lstar/fork_choice.py`; vote tie-breaks are insertion-order independent since leanEthereum/leanSpec#1181)
  - Note: Computes the canonical head root from the Store using LMD-GHOST.
  - Proved at: `LeanSpec/Forks/Lstar/Store/Store.lean` (`Store.update_head_deterministic`; well-definedness as `Store.computeLmdGhostHead_in_store` / `Store.updateHead_head_in_store` — the selected head is the justified anchor or a stored block — with totality by fuel-bounded construction)
  - Sample code:

    ```lean
    theorem compute_head_deterministic (st : Store) :
        Store.computeHead st = Store.computeHead st := by rfl
    -- In practice: expand into a separate lemma proving well-formedness as a pure function.
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/Store.lean as
    --    `Store.update_head_deterministic` (upstream renamed `compute_head` →
    --    `update_head`; substance in `Store.computeLmdGhostHead_in_store` and
    --    `Store.updateHead_head_in_store`)
    ```

- [x] **FC-2: The head descends from the latest justified checkpoint**
  - Source: `compute_head` (derived property; same function as FC-1 — upstream `update_head` / `_compute_lmd_ghost_head`)
  - Note: Confirm that the head is a descendant of justified using the helper `isAncestorOrEqual` (decides whether `a` is an ancestor of, or equal to, `b`). Modeled relationally as `Store.AncestorOrEqual` (`a = d ∨ ProperAncestor st a d`), like FC-4's `ProperAncestor`.
  - Proved at: `LeanSpec/Forks/Lstar/Store/Ancestry.lean` (`Store.head_descends_from_justified`, via `Store.ghostWalk_ancestorOrEqual` — every walk step moves to a stored child — and `Store.computeLmdGhostHead_descends`; `ProperAncestor.trans` composes the steps)
  - Sample code:

    ```lean
    theorem head_descends_from_justified (st : Store) (h : Bytes32)
        (hh : Store.computeHead st = h) :
        Store.isAncestorOrEqual st st.latestJustified.root h := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/Ancestry.lean as
    --    `Store.head_descends_from_justified` (stated directly on
    --    `(Store.updateHead st).head` under `Store.WellFormed`)
    ```

- [x] **FC-3: An attestation's source / target / head are slot-ordered**
  - Source: `validate_attestation` (`src/lean_spec/spec/forks/lstar/fork_choice.py`; since leanEthereum/leanSpec#1179 it also rejects heads off the finalized subtree — `HEAD_NOT_DESCENDANT_OF_FINALIZED` — closing the vote-resurrection gap of issue #1176 M-2)
  - Note: Validates the consistency of an attestation (slot ordering, existence of referenced blocks, checkpoint-block slot consistency, ancestry, head observability, clock-skew admission horizon).
  - Proved at: `LeanSpec/Forks/Lstar/Store/Store.lean` (`Store.attestation_topology`, from the topology checks of `Store.validateAttestation`)
  - Sample code:

    ```lean
    theorem attestation_topology
        (st : Store) (att : Attestation)
        (h : Store.validateAttestation st att = .ok) :
        att.data.source.slot ≤ att.data.target.slot ∧
        att.data.target.slot ≤ att.data.head.slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/Store.lean as
    --    `Store.attestation_topology` (mirroring upstream, the modeled
    --    function takes the `AttestationData` directly and returns
    --    `.ok ()`)
    ```

- [x] **FC-4: The fork-choice tree is acyclic**
  - Source: `Database.add_block` / `parent_root` convention (a structural invariant established at block-insertion time; realized as `Store.WellFormed.parentSlotLt` — `on_block` runs the STF, which admits only strictly-future slots)
  - Note: Uses `isProperAncestor` (decides whether `a` is a strict ancestor of `b`, i.e. `a ≠ b`) and expresses acyclicity by negating "a block is a strict ancestor of itself". Modeled relationally as the inductive `Store.ProperAncestor` (the deciding walk is `checkpointIsAncestor`'s; the acyclicity argument needs the derivation, not the decision procedure).
  - Proved at: `LeanSpec/Forks/Lstar/Store/Ancestry.lean` (`Store.fork_choice_acyclic`, via `Store.properAncestor_slot_lt` — slots strictly decrease along every parent step)
  - Sample code:

    ```lean
    theorem fork_choice_acyclic (st : Store) (hwf : Store.WellFormed st) :
        ∀ b ∈ st.blocks.values, ¬ Store.isProperAncestor st b.root b.root := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/Ancestry.lean as
    --    `Store.fork_choice_acyclic` (blocks are keyed pairs, so the statement
    --    quantifies `∀ p ∈ st.blocks, ¬ Store.ProperAncestor st p.1 p.1`)
    ```

- [x] **FC-5: The block-production iteration terminates in finitely many steps**
  - Source: `produce_block_with_signatures` (realized as `build_block` in current leanSpec, `src/lean_spec/spec/forks/lstar/block_production.py`; candidate order and tie-breaks content-derived since leanEthereum/leanSpec#1181)
  - Note: Because attestations included in a new block can update the justified slot, the proposer iterates: "rebuild the block based on the current justified → if justified moves, rebuild again". The proposition asserts that this iteration terminates in finitely many rounds (i.e. reaches a fixed point) thanks to the monotone non-decreasing nature of the justified slot together with an upper bound.
  - Proved at: `LeanSpec/Forks/Lstar/Store/BlockProduction.lean`. Termination is witnessed by `BlockProduction.selectionLoop`, defined by well-founded recursion on the unprocessed candidate count with **no fuel** — the decreasing measure (`selectionPass_rest_lt`: a pass that accepted something strictly shrinks the remainder) is exactly upstream's "the chosen set only grows, and is bounded". The explicit finite-rounds statement is `build_block_selection_terminates`: at most `payloads.length + 1` passes, for any coverage picker (`select_proofs_for_coverage` is a parameter — its choices never steer the loop's control flow).
  - Sample code: expressed via `WellFoundedRecursion`. High difficulty.

    ```lean
    -- ✅ realized in LeanSpec/Forks/Lstar/Store/BlockProduction.lean:
    --    `selectionLoop` (well-founded recursion, no fuel) and
    --    `build_block_selection_terminates` (pass count ≤ candidates + 1)
    ```

- [x] **FC-6: `update_head` preserves the store invariants**
  - Source: `update_head` (`src/lean_spec/spec/forks/lstar/fork_choice.py`; the finalized re-derivation loop, with the `Checkpoint.advance_to` / `Store.latest_finalized` invariant notes of leanEthereum/leanSpec#1179)
  - Note: `update_head` rewrites only `head` and `latest_finalized`, so five of the six `Store.WellFormed` clauses carry over untouched. The substantive clause is `justifiedDescendsFromFinalized`: the re-derived finalized checkpoint — the head chain's ancestor at the head state's finalized slot — must still sit on the justified chain. Proved from FC-2 (the head descends from the justified root), a descent lemma for the re-derivation walk, comparability of two ancestors of one block (parent links are unique), and completeness of the Boolean `_checkpoint_is_ancestor` walk against the relational ancestry (the fuel argument counts distinct stored blocks at or below the walk's position, which strictly shrinks each step). Two store invariants that `on_block` maintains outside `update_head`'s reach enter as explicit hypotheses rather than growing `WellFormed`: the justified checkpoint records its own block's slot, and no stored post-state finalizes past the store's justified slot (via ST-4).
  - Proved at: `LeanSpec/Forks/Lstar/Store/Ancestry.lean` (`Store.updateHead_wellFormed`; via `properAncestor_comparable` / `ancestors_comparable`, `descendToSlot_ancestorOrEqual`, `ancestorWalk_complete`, and `checkpointIsAncestor_of_ancestorOrEqual`)
  - Sample code:

    ```lean
    theorem updateHead_wellFormed (st : Store) (hwf : Store.WellFormed st)
        (hjslot : ∀ bj, st.getBlock? st.latestJustified.root = some bj →
          bj.slot = st.latestJustified.slot)
        (hdom : ∀ r s₀, st.getState? r = some s₀ →
          s₀.latestFinalized.slot ≤ st.latestJustified.slot) :
        Store.WellFormed (Store.updateHead st) := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/Ancestry.lean as
    --    `Store.updateHead_wellFormed`
    ```

- [x] **FC-7: `on_block` preserves the store invariants**
  - Source: `on_block` (`src/lean_spec/spec/forks/lstar/fork_choice.py`, post leanEthereum/leanSpec#1182)
  - Note: Closes the loop FC-6 opened: `on_block` is the mutator that maintains the two side conditions FC-6 consumes, so the composition `on_block → update_head` preserves `Store.WellFormed` together with the new alignment bundle `Store.Aligned` (stored states sit at their block's slot and satisfy ST-4; the justified checkpoint records its block's slot; no stored state finalizes past the store's justified slot). The model (`Store.onBlock`) mirrors the upstream gate sequence — known-block skip, parent-state gate, #1182 gap/horizon guards, duplicate-attestation rejection, STF, import writes, `advance_to`, `update_head`, conditional pruning. Modeled divergences: `hash_tree_root(block)` enters as the `blockRoot` parameter, XMSS signature verification is omitted (Arklib-side; it only rejects more blocks), and pruning is a parameter constrained to leave blocks/states/checkpoints unchanged. Residual hypotheses (documented in the theorem docstring): no stored block already names the incoming root as parent (STOR-1 + hash acyclicity upstream), and — when the STF advances the justified checkpoint — the new checkpoint names an imported block at its own slot and descends from the finalized checkpoint. The latter is the **historical-chain alignment layer** (`historical_block_hashes` mirroring the block map), the next modeling milestone.
  - Proved at: `LeanSpec/Forks/Lstar/Store/OnBlock.lean` (`Store.onBlock_wellFormed`, via `Store.applyBlock_invariants`; walk stability as `ancestorWalk_extend` / `ancestorWalk_fuel_mono` / `checkpointIsAncestor_applyBlock`; transfer lemmas `wellFormed_congr` / `aligned_congr`; the STF slot lemma as `State.transition_state_slot`)
  - Sample code:

    ```lean
    theorem onBlock_wellFormed
        (prune : Store → Store) (hprune : ...) (st st' : Store)
        (blockRoot : Root) (b : Block)
        (hwf : Store.WellFormed st) (hal : Store.Aligned st)
        (hfreshParent : ∀ p ∈ st.blocks, p.2.parentRoot ≠ blockRoot)
        (hjnew : ...)
        (h : Store.onBlock prune st blockRoot b = .ok st') :
        Store.WellFormed st' ∧ Store.Aligned st' := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/OnBlock.lean as
    --    `Store.onBlock_wellFormed`
    ```

- [x] **FC-8: Stored histories mirror the block map (the chain-alignment layer)**
  - Source: `process_block_header` (history append) / `process_attestations` (`lies_on_chain` filter) / `on_block` (import writes); `src/lean_spec/spec/forks/lstar/state_transition.py` and `fork_choice.py`
  - Note: Discharges the stored half of FC-7's residual `hjnew` hypothesis. STF level (`LeanSpec/Forks/Lstar/HistoryAlignment.lean`): the post-history is the parent history, then the parent root, then one zero hash per skipped slot (`transition_hist`, sized to the block's slot by `transition_hist_size`), and the justified checkpoint moves only onto that history — it stays, anchors at slot 0, or lands at its own slot with a non-zero root (`transition_justified_on_chain`, via the `lies_on_chain` filter). Store level: `Store.ChainAligned` — stored histories are sized to their state's slot, every non-zero entry names a stored block at exactly that slot, and no stored state's justified slot outruns the store's; `on_block` maintains all of it, so an STF-advanced justified checkpoint always names an imported block at its own slot (`applyBlock_justified_stored`). The **descent half** of `hjnew` remains the explicit `hjdesc` hypothesis of `onBlock_invariants`: it is *not* a history fact — a competing fork's state can justify a checkpoint off the finalized subtree unless a 2/3-quorum argument (accountable safety) excludes conflicting supermajorities. That quorum layer is the catalog's known open frontier.
  - Proved at: `LeanSpec/Forks/Lstar/HistoryAlignment.lean` (STF lemmas) and `LeanSpec/Forks/Lstar/Store/ChainAlignment.lean` (`Store.ChainAligned`, `Store.applyBlock_chainAligned`, `Store.applyBlock_justified_stored`, `Store.onBlock_invariants`)
  - Sample code:

    ```lean
    theorem onBlock_invariants
        (prune : Store → Store) (hprune : ...) (st st' : Store)
        (blockRoot : Root) (b : Block)
        (hwf : Store.WellFormed st) (hal : Store.Aligned st)
        (hcal : Store.ChainAligned st)
        (hfreshParent : ∀ p ∈ st.blocks, p.2.parentRoot ≠ blockRoot)
        (hjdesc : ...)  -- the quorum-level descent assumption
        (h : Store.onBlock prune st blockRoot b = .ok st') :
        Store.WellFormed st' ∧ Store.Aligned st' ∧
        Store.ChainAligned st' := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Store/ChainAlignment.lean as
    --    `Store.onBlock_invariants`
    ```

## Validator

A **Validator** is an entity that stakes ETH and participates in consensus. At each slot it executes its assigned **duties**: (1) propose a new block if selected as `proposer`, and (2) vote on the current head as an `attester`. The validator service locally manages its keys (a dual-key configuration with a proposal key and an attestation key) and signed history.

The propositions here guarantee **duty correctness and slashing prevention**: proposer selection is round-robin via `slot mod n`, with exactly one proposer per slot; the proposal key and attestation key are distinct (so key compromise stays local); no double-voting in the same slot (double voting is slashable); the stateful XMSS signing key never moves its used index backwards (key reuse leaks the secret key); and so on. These are the conditions for a validator to avoid penalties while letting the network advance safely. Implementations live in `LeanSpec/Validator/*`.

- [x] **VAL-1: Proposers are selected round-robin**
  - Source: `proposer_index` (in `process_block_header`; realized as `ValidatorIndex.proposer_for_slot` in `src/lean_spec/spec/forks/lstar/containers/identifiers.py`)
  - Note: Returns the proposer index for a given slot from the slot and the number of active validators `n` (round-robin).
  - Proved at: `LeanSpec/Forks/Lstar/Containers/Identifiers.lean` (`ValidatorIndex.proposer_index_round_robin`; `proposerForSlot_toNat` shows the `UInt64` construction never wraps). `processBlockHeader` consumes `proposerForSlot`, so the theorem speaks about the deployed selection.
  - Sample code (`proposerFor` realized as `proposerForSlot` mirroring the Python name; `ValidatorIndex.mk` as `UInt64.ofNat`):

    ```lean
    theorem proposer_index_round_robin (slot : Slot) (n : Nat) (h : 0 < n) :
        ValidatorIndex.proposerFor slot n = ValidatorIndex.mk (slot.toNat % n) := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Containers/Identifiers.lean as
    --    `ValidatorIndex.proposer_index_round_robin`
    ```

- [x] **VAL-2: Proposal key and attestation key are distinct**
  - Source: `proposalKey` / `attestationKey` (ValidatorService; realized as the `attestation_secret_key` / `proposal_secret_key` fields of `ValidatorEntry`, `src/lean_spec/node/validator/registry.py`)
  - Note: Each validator manages two separate signing keys, one for block proposal and one for attestations — documented upstream as "without OTS conflict". Originally **not enforced** (`ValidatorRegistry.add` assigned without validation, `from_yaml` compared nothing, so a same-key manifest loaded silently and one slot's proposal + attestation signatures would consume overlapping XMSS one-time-signature state); found by attempting this proposition and reported upstream as leanEthereum/leanSpec#1184 (the "invariant maintained only by convention" class of #1176). **Enforced since leanEthereum/leanSpec#1185**: the loader rejects a manifest whose two public keys coincide, before touching secret bytes, so every loaded registry satisfies `WellFormed` by construction.
  - Proved at: `LeanSpec/Validator/Registry.lean` (`ValidatorRegistry.dual_key_distinct`, relative to `WellFormed`; `WellFormed.add` shows unchecked insertion preserves the invariant; `addChecked` mirrors the merged #1185 public-key check with the derivation as a parameter — `addChecked_wellFormed` for every derivation, `addChecked_seed_distinct` for seed-fingerprinting ones)
  - Sample code:

    ```lean
    theorem dual_key_distinct (vid : ValidatorIndex) (reg : KeyRegistry) :
        reg.proposalKey vid ≠ reg.attestationKey vid := by sorry
    -- ✅ proved in LeanSpec/Validator/Registry.lean as
    --    `ValidatorRegistry.dual_key_distinct` (relative to
    --    `ValidatorRegistry.WellFormed` — established at load time by
    --    upstream since leanEthereum/leanSpec#1185, mirrored as
    --    `addChecked_wellFormed`)
    ```

- [x] **VAL-3: Each slot has exactly one proposer**
  - Source: `is_proposer` / `proposer_index` (ValidatorService; the check in use is equality with `proposer_for_slot`, e.g. in `validator_duties.py`)
  - Note: Decides whether validator `vid` is the proposer of `slot` (equivalent to `vid = slot mod n`).
  - Proved at: `LeanSpec/Forks/Lstar/Containers/Identifiers.lean` (`ValidatorIndex.unique_proposer`; `∃!` written in expanded form since `ExistsUnique` is Mathlib-only)
  - Sample code:

    ```lean
    theorem unique_proposer (slot : Slot) (n : Nat) (h : 0 < n) :
        ∃! vid : Fin n, ValidatorIndex.isProposerFor vid slot := by sorry
    -- ✅ proved in LeanSpec/Forks/Lstar/Containers/Identifiers.lean as
    --    `ValidatorIndex.unique_proposer` (∃! expanded: ∃ vid, P vid ∧ ∀ vid', P vid' → vid' = vid)
    ```

- [x] **VAL-4: Double-voting in the same slot is impossible**
  - Source: `ValidatorService.produce_attestation` (realized as the attestation arm of `ValidatorService.run` in `src/lean_spec/node/validator/service.py`: the duty gate over the service-wide `_attested_slots` set)
  - Note: Checks the local history for "already attested in this slot"; produces a new attestation only if not yet voted. Upstream tracks attested slots per service — one attestation pass covers every validator the node manages — and the gate silently skips rather than failing, retrying gated slots on later passes; modeled as `attestationDutyStep = none`.
  - Proved at: `LeanSpec/Validator/Service.lean` (`ValidatorService.no_double_vote`; `attested_after_duty` shows a fired duty records its slot through the retention prune, and `no_double_vote_after` sharpens VAL-4 to "once fired, never again for that slot")
  - Sample code:

    ```lean
    theorem no_double_vote
        (svc svc' : ValidatorService) (vid : ValidatorIndex) (slot : Slot)
        (hin : slot ∈ svc.attestedSlots vid)
        (h : ValidatorService.produceAttestation svc vid slot = .ok svc') :
        False := by sorry
    -- ✅ proved in LeanSpec/Validator/Service.lean as
    --    `ValidatorService.no_double_vote` (the attested set is
    --    service-wide upstream, not per validator, and the gate skips
    --    instead of erroring: `attestationDutyStep ... = none`)
    ```

- [x] **VAL-5: XMSS preparation state is monotonically increasing**
  - Source: `XMSS.advance_preparation` (called from ValidatorService; realized as `GeneralizedXmssScheme.advance_preparation`, `src/lean_spec/spec/crypto/xmss/interface.py`, with the window fields on `SecretKey` in `crypto/xmss/containers.py`)
  - Note: Advances the prepared state of the XMSS secret key (the range of usable one-time keys) by one step. `preparedEnd` is the last index currently prepared. Upstream returns the key **unchanged** once the next window would exceed the activation interval, so the sample's unconditional strict `<` is false as written: the unconditional truth is `≤` (the window never rewinds — the slashing-safety core), with strictness inside the activation interval.
  - Proved at: `LeanSpec/Validator/Xmss.lean` (`Scheme.advancePreparation_monotone` — unconditional `≤`; `Scheme.advancePreparation_strict_mono` — the catalog's `<` under its true precondition; `Scheme.advancePreparation_exhausted` — fixed point past activation). The Phase-2 tree regeneration is a parameter (Arklib side), so all three hold for every regenerator.
  - Sample code:

    ```lean
    theorem xmss_advance_monotone (sk : XMSSSecretKey) :
        sk.preparedEnd < (XMSS.advancePreparation sk).preparedEnd := by sorry
    -- ✅ proved in LeanSpec/Validator/Xmss.lean as
    --    `Scheme.advancePreparation_strict_mono` (strict form needs the
    --    activation interval to still have room; the unconditional half
    --    is `Scheme.advancePreparation_monotone`, a `≤`)
    ```

## Networking

**Networking** is the inter-peer communication protocol. There are two systems: (1) **req/resp** — synchronous 1:1 RPCs such as `BlocksByRange`, `BlocksByRoot`, `Status`; (2) **gossipsub** — publish/subscribe message propagation for `beacon_block`, `beacon_attestation`, etc. Both run on top of libp2p.

The propositions here guarantee **bound values for DoS resistance**: a `BlocksByRange` response does not exceed the smaller of the requested `count` and `MAX_REQUEST_BLOCKS`; a decodable payload is no larger than `MAX_PAYLOAD_SIZE`; etc. If these break, a malicious peer can exhaust a node's memory/CPU by sending huge payloads or unbounded responses. Implementations live in `LeanSpec/Networking/*`.

- [x] **NET-1: BlocksByRange response length never exceeds the bound**
  - Source: `Handler.handle` (BlocksByRange; realized as `RequestHandler.handle_blocks_by_range`, `src/lean_spec/node/networking/reqresp/handler.py`)
  - Note: A req/resp handler that receives a `BlocksByRange` request and responds with a list of blocks. Upstream additionally rejects a count of zero, refuses requests below the sliding history window (`MIN_SLOTS_FOR_BLOCK_REQUESTS`), and silently skips empty slots; the configured lookup callbacks enter the model as parameters.
  - Proved at: `LeanSpec/Networking/ReqResp.lean` (`blocks_by_range_bounded`)
  - Sample code:

    ```lean
    theorem blocks_by_range_bounded
        (req : BlocksByRangeRequest) (resp : List Block)
        (h : Handler.handle req = .ok resp) :
        resp.length ≤ min req.count MAX_REQUEST_BLOCKS := by sorry
    -- ✅ proved in LeanSpec/Networking/ReqResp.lean as
    --    `blocks_by_range_bounded` (the wire type is `SignedBlock`, and
    --    the handler takes the two configured lookups as parameters)
    ```

- [x] **NET-2: A decodable payload size is at most the upper bound**
  - Source: `Codec.decode` (realized as `RequestHandler._read_request`, `src/lean_spec/node/networking/reqresp/handler.py`: the `[varint_length][snappy_framed_payload]` reader — the attacker-controlled declared length is gated at `MAX_PAYLOAD_SIZE` before any buffer is sized, and a decode succeeds only when the decompressed size equals the declared length)
  - Note: SSZ-decodes a message payload on the req/resp protocol into the `Message` type. Snappy enters the model as the `decompress` parameter, so the bounds hold for every decompressor.
  - Proved at: `LeanSpec/Networking/ReqResp.lean` (`payload_size_bound`; the wire-side buffering bound as `compressed_size_bound` — accepted compressed bytes never exceed snappy's worst-case expansion of an in-bound payload)
  - Sample code:

    ```lean
    theorem payload_size_bound (payload : ByteArray) (msg : Message)
        (h : Codec.decode payload = .ok msg) :
        payload.size ≤ MAX_PAYLOAD_SIZE := by sorry
    -- ✅ proved in LeanSpec/Networking/ReqResp.lean as `payload_size_bound`
    --    (stated on `readRequest`, the reader's pure terminal state; the
    --    decoded message carries the bound, and `compressed_size_bound`
    --    bounds the wire bytes)
    ```

## Storage

**Storage** is the persistence layer — it saves blocks, states, and checkpoints to disk and is responsible for restart recovery and pruning. In practice, on top of a `Database` interface that abstracts a KV store (LevelDB / RocksDB family), it manages the `block_root → Block` and `state_root → BeaconState` mappings.

The propositions here guarantee **chain-structure consistency and write atomicity**: every block in the store, except genesis, has its parent in the store as well (no orphan blocks; this is a fork-choice precondition); `batch_write` is in only one of two states — fully successful or fully failed (so partial persistence cannot leave state and block references inconsistent); and so on. If these break, the Store becomes corrupted after restart and fork choice cannot run. Implementations live in `LeanSpec/Storage/*`.

- [x] **STOR-1: Every non-genesis Block has its parent in the store**
  - Source: `Database.add_block` (parent-existence precondition; no such database method exists in current leanSpec — the gate is `on_block`'s `UNKNOWN_PARENT_BLOCK` rejection in `src/lean_spec/spec/forks/lstar/fork_choice.py`, which runs before `SyncService._persist_block` writes anything)
  - Note: Each block in the store has a parent block root (`parent_root`); for non-genesis blocks the parent must exist in `store.blocks` (the `block_root → Block` map). The exception generalizes beyond genesis: `create_store` seeds the map with a chain anchor whose parent is outside the tree (zero hash for genesis, an absent block for a checkpoint-sync anchor), so the invariant is stated relative to the anchor root.
  - Proved at: `LeanSpec/Storage/Blocks.lean` (`Store.parentsPresent_anchor` establishes the invariant at anchoring, `Store.parentsPresent_insertBlock` shows the parent-gated insertion preserves it — the gate reads the states map as upstream does, so the #1176 M-4 blocks-states alignment enters as a hypothesis — and `Store.parent_exists_or_genesis` is the catalog form on a genesis-anchored store). `insertBlock` also carries the horizon guards of leanEthereum/leanSpec#1182 (merged as `4ca7d27e`, fixing issue #1171): `insertBlock_slot_gap_bounded` and `insertBlock_within_horizon` bound an accepted block's slot against the parent and the store clock.
  - Sample code:

    ```lean
    theorem parent_exists_or_genesis
        (st : Store) (b : Block)
        (hin : b ∈ st.blocks.values) :
        b.parentRoot = ByteArray.zeroes 32 ∨
        st.blocks.contains b.parentRoot := by sorry
    -- ✅ proved in LeanSpec/Storage/Blocks.lean as
    --    `Store.parent_exists_or_genesis` (relative to the
    --    `ParentsPresent` anchor invariant, established and preserved by
    --    `parentsPresent_anchor` / `parentsPresent_insertBlock`)
    ```

- [x] **STOR-2: Batch writes are atomic**
  - Source: `Database.batch_write` (`src/lean_spec/node/storage/database.py`; deployed in `sqlite.py` — commits on clean exit, rolls back on any exception)
  - Note: Applies multiple writes in a single transaction (atomic guarantee: all-or-nothing). Modeled as a fold through a working copy: commit returns the fully-written copy, the error path returns no database at all — the caller's pre-batch value is untouched by construction, which is the pure-model rollback. Backend write failures (`sqlite3.Error`) enter as the `writeOk` parameter.
  - Proved at: `LeanSpec/Storage/Database.lean` (`Database.batch_write_commits` — every write of a committed batch is contained, for batches without key collisions; `Database.batch_atomic` — the catalog disjunction)
  - Sample code (high-level model):

    ```lean
    theorem batch_atomic
        (db db' : Database) (ws : List Write) :
        Database.batchWrite db ws = .ok db' →
        (∀ w ∈ ws, db'.contains w) ∨ db' = db := by sorry
    -- ✅ proved in LeanSpec/Storage/Database.lean as `Database.batch_atomic`
    --    (with distinct write keys — a later write to the same key
    --    overwrites — and the backend failure model as a parameter)
    ```

## Sync

**Sync** is a finite state machine (FSM) that manages the process of a node catching up to the network's latest head. Three states: `IDLE` (just after start-up or while stopped; does not process blocks), `SYNCING` (significantly behind the head; fetching ranges via req/resp), and `SYNCED` (caught up; receiving in real time via gossip). Only four transitions are permitted: `IDLE → SYNCING`, `SYNCING → SYNCED`, `SYNCED → SYNCING` (fell behind again), and from any state to `IDLE` (shutdown / fatal).

The propositions here guarantee **closure of the FSM and gating of gossip**: the implementation's `transition` function never produces transitions outside the four allowed ones; `acceptsGossip ⇔ st ∈ {SYNCING, SYNCED}` (accepting gossip while `IDLE` would re-forward stale/broken payloads and pollute the network); and so on. Implementations live in `LeanSpec/Sync/*`.

- [x] **SYNC-1: The sync FSM only takes the four permitted transitions**
  - Source: `SyncService.transition` (realized as `SyncService._transition_to`, `src/lean_spec/node/sync/service.py`, over `SyncState` in `node/sync/states.py`)
  - Note: Computes the next state of the sync FSM from the current state (one of the four permitted transitions, or `none`). Upstream validates a *requested* move rather than computing it — rejecting self-transitions and the `IDLE → SYNCED` shortcut, accepting everything else — which is **stricter** than this relation: `any_to_idle` admits the idle self-loop, `_transition_to` rejects every self-loop (`transitionTo_ne`).
  - Proved at: `LeanSpec/Sync/States.lean` (`SyncState.transition_sound`; the extra strictness as `SyncState.transitionTo_ne`)
  - Sample code:

    ```lean
    inductive SyncState | idle | syncing | synced
    inductive SyncState.canTransitionTo : SyncState → SyncState → Prop
      | idle_to_syncing : canTransitionTo .idle .syncing
      | syncing_to_synced : canTransitionTo .syncing .synced
      | synced_to_syncing : canTransitionTo .synced .syncing
      | any_to_idle (s) : canTransitionTo s .idle

    theorem transition_sound (s s' : SyncState)
        (h : SyncService.transition s = some s') :
        s.canTransitionTo s' := by sorry
    -- ✅ proved in LeanSpec/Sync/States.lean as `SyncState.transition_sound`
    --    (the guard takes the requested state as an argument:
    --    `transitionTo s n = some s'`)
    ```

- [x] **SYNC-2: Gossip is accepted only in SYNCING / SYNCED**
  - Source: `SyncService.accepts_gossip` (realized as the `SyncState.accepts_gossip` property, `src/lean_spec/node/sync/states.py`; every `on_gossip_*` handler in `node/sync/service.py` checks it first)
  - Note: Decides whether the current state accepts gossipsub messages (true only for `SYNCING` or `SYNCED`).
  - Proved at: `LeanSpec/Sync/States.lean` (`SyncState.accepts_gossip_iff`)
  - Sample code:

    ```lean
    theorem accepts_gossip_iff (st : SyncState) :
        SyncService.acceptsGossip st ↔ st = .syncing ∨ st = .synced := by sorry
    -- ✅ proved in LeanSpec/Sync/States.lean as `SyncState.accepts_gossip_iff`
    ```
