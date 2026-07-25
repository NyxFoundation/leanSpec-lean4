/-
Chain and consensus configuration constants.

Mirrors `src/lean_spec/spec/forks/lstar/config.py` in leanSpec. Only the
constants consumed by the ported logic are declared; SSZ list limits
(`VALIDATOR_REGISTRY_LIMIT`, …) are not enforced by the Lean `Array`
model and are added when a proposition needs them.
`HISTORICAL_ROOTS_LIMIT` is declared below not as a list limit but
because the fork-choice horizon guards bound a block's slot gap by it.

Supports the ST-* propositions from `docs/lean4-proof-propositions.md`
(no theorems in this file).
-/

namespace LeanSpec.Forks.Lstar

/-- Maximum number of distinct attestation data entries per block
(`MAX_ATTESTATIONS_DATA`, a `Uint8` upstream). -/
def MAX_ATTESTATIONS_DATA : Nat := 8

/-- Number of validator-duty intervals per slot
(`INTERVALS_PER_SLOT`, a `Uint64` upstream). -/
def INTERVALS_PER_SLOT : Nat := 5

/-- Clock-skew margin for gossip admission, in intervals — one interval,
deliberately not a whole slot (`GOSSIP_DISPARITY_INTERVALS`, a `Uint64`
upstream). -/
def GOSSIP_DISPARITY_INTERVALS : Nat := 1

/-- SSZ limit on the historical-roots list, doubling as the bound on how
far a block's slot may run beyond its parent
(`HISTORICAL_ROOTS_LIMIT`, a `Uint64` upstream). -/
def HISTORICAL_ROOTS_LIMIT : Nat := 2 ^ 18

end LeanSpec.Forks.Lstar
