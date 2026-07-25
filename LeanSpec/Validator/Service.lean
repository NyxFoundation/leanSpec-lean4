/-
Validator attestation duty gate.

Mirrors the attestation arm of `ValidatorService.run` in
`src/lean_spec/node/validator/service.py` (post
leanEthereum/leanSpec#1180, which typed the duty-path errors):
  - `_attested_slots` — slots this service has already attested,
    service-wide: one attestation pass covers every validator the node
    manages, so the gate is per service, not per validator.
  - the duty gate — attest only from interval 1 on, only when synced
    for duties, and only when the slot is not already attested; a gated
    slot stays unattested and retries on a later pass.
  - the retention prune — after attesting, slots older than
    `ATTESTED_SLOT_RETENTION` below the current slot are dropped to
    bound memory (`max(0, slot - retention)`; the truncated `Nat`
    subtraction is Python's clamp).

The service around the gate is node runtime: the async clock loop, the
sync service, the gossip publishers, and the metrics counters. The
gate's two inputs from that runtime — the current interval and the
`_is_synced_for_duties` verdict — enter as plain arguments, and the
attestation production itself (signing, local import, publishing) is IO
outside the modeled state step.

Proves VAL-4 from `docs/lean4-proof-propositions.md`:
  - VAL-4: double-voting in the same slot is impossible — the duty gate
    never fires for an already-attested slot (`no_double_vote`); a
    fired duty records its slot through the retention prune
    (`attested_after_duty`); hence the gate can never fire twice for
    one slot (`no_double_vote_after`).
-/

import LeanSpec.Forks.Lstar.Containers.Interval

namespace LeanSpec.Validator

open LeanSpec.Forks.Lstar (Interval)

/-- Slots an attested slot is retained for after its own
(`ATTESTED_SLOT_RETENTION`, an `int` upstream, defined in
`service.py`).

The duty always attests the *current* slot (`slot = clock.current_slot()`),
so once the clock advances a past slot can never be attested again and its
dedup entry is dead weight — the set fundamentally only needs the current
slot to block a second vote across the slot's `INTERVALS_PER_SLOT` passes.
The value `4` is therefore a conservative margin absorbing loop lag (a slow
duty spilling across slots) and clock jitter, not a figure the upstream spec
derives from a formula. Safety does not depend on it: `attested_after_duty`
uses only `threshold = slot - RETENTION ≤ slot`, which holds for every
`RETENTION` under truncated `Nat` subtraction, so the value tunes the
memory/margin trade-off, never the double-vote guarantee. -/
def ATTESTED_SLOT_RETENTION : Nat := 4

/-- The duty-relevant validator-service state: the slots this service
has already attested (`_attested_slots`). The runtime fields are IO —
see the module docstring. -/
structure ValidatorService where
  attestedSlots : List Slot
  deriving Inhabited, Repr

namespace ValidatorService

/-- Drop attested slots too old to attest again
(`prune_threshold = Slot(max(0, int(slot) - ATTESTED_SLOT_RETENTION))`,
then keep the slots at or above it). -/
def pruneAttested (slot : Slot) (attested : List Slot) : List Slot :=
  let threshold : Slot := UInt64.ofNat (slot.toNat - ATTESTED_SLOT_RETENTION)
  attested.filter (fun s => threshold ≤ s)

/-- Whether the attestation duty fires (`run`'s gate): from interval 1
on, at most once per slot, and only when synced for duties. -/
def attestationDue (svc : ValidatorService) (slot : Slot)
    (interval : Interval) (synced : Bool) : Bool :=
  decide ((1 : Interval) ≤ interval) &&
  !(svc.attestedSlots.contains slot) &&
  synced

/-- One pass of the attestation arm of the duty loop: `none` when the
gate holds the duty back (upstream falls through and may retry the slot
on a later pass), `some` with the slot recorded and the retention
window pruned when the duty fires. -/
def attestationDutyStep (svc : ValidatorService) (slot : Slot)
    (interval : Interval) (synced : Bool) : Option ValidatorService :=
  if attestationDue svc slot interval synced then
    some { svc with
      attestedSlots := pruneAttested slot (slot :: svc.attestedSlots) }
  else
    none

/-- VAL-4: the duty gate never fires for an already-attested slot — a
second attestation for the same slot is impossible. -/
theorem no_double_vote (svc : ValidatorService) (slot : Slot)
    (interval : Interval) (synced : Bool)
    (hin : svc.attestedSlots.contains slot = true) :
    attestationDutyStep svc slot interval synced = none := by
  unfold attestationDutyStep attestationDue
  rw [hin]
  simp

/-- The freshly attested slot survives its own retention prune: the
threshold sits at or below the slot itself. -/
theorem attested_after_duty (svc svc' : ValidatorService) (slot : Slot)
    (interval : Interval) (synced : Bool)
    (h : attestationDutyStep svc slot interval synced = some svc') :
    svc'.attestedSlots.contains slot = true := by
  unfold attestationDutyStep at h
  split at h
  · injection h with h'
    subst h'
    have hth : (UInt64.ofNat (slot.toNat - ATTESTED_SLOT_RETENTION)) ≤ slot := by
      have hlt := slot.toNat_lt
      have hsz : UInt64.size = 2 ^ 64 := rfl
      rw [UInt64.le_iff_toNat_le, UInt64.toNat_ofNat_of_lt' (by omega)]
      omega
    show (pruneAttested slot (slot :: svc.attestedSlots)).contains slot = true
    unfold pruneAttested
    rw [List.contains_iff_mem]
    exact List.mem_filter.mpr ⟨List.mem_cons_self, by simpa using hth⟩
  · exact absurd h (by simp)

/-- VAL-4, sharpened: once the duty fired for a slot, no later pass can
fire for that slot again — regardless of interval or sync verdict. -/
theorem no_double_vote_after (svc svc' : ValidatorService) (slot : Slot)
    (interval interval' : Interval) (synced synced' : Bool)
    (h : attestationDutyStep svc slot interval synced = some svc') :
    attestationDutyStep svc' slot interval' synced' = none :=
  no_double_vote svc' slot interval' synced'
    (attested_after_duty svc svc' slot interval synced h)

end ValidatorService
end LeanSpec.Validator
