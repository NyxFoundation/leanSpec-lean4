/-
Normative allocation bounds for the req/resp reader.

The proven acceptance bounds (NET-1/NET-2, `ReqResp.lean`) imply exact
worst-case buffer sizes, but upstream leanSpec never names them: each
client picks its own buffer strategy for the
`[varint_length][snappy_framed_payload]` wire format
(`src/lean_spec/node/networking/reqresp/codec.py`,
`.../varint.py`). Issue #70 asks for the closed-form constants and the
theorems tying them to the reader model, as the basis for an upstream
proposal: "clients MAY preallocate X bytes per req/resp stream; a
conforming reader never buffers more".

Constants (with their concrete values, proved by `rfl`):
  - `MAX_COMPRESSED_PAYLOAD_SIZE` — snappy's worst-case expansion of a
    maximal in-bound payload (`n + n/6 + 1024` at
    `n = MAX_PAYLOAD_SIZE`): 12 234 410 bytes.
  - `MAX_LENGTH_PREFIX_SIZE` — the LEB128 varint for any accepted
    declared length fits in 4 bytes (`128^4 > MAX_PAYLOAD_SIZE`).
  - `MAX_REQUEST_WIRE_SIZE` — their sum, 12 234 414 bytes: the total
    wire allocation one accepted request can require.

Theorems:
  - `varintSize_le_prefix_bound` — an in-bound declared length encodes
    in at most `MAX_LENGTH_PREFIX_SIZE` varint bytes (`varintSize`
    mirrors `encode_varint`'s 7-bit-group loop).
  - `request_wire_bound` — for any accepted request, length prefix plus
    compressed payload never exceed `MAX_REQUEST_WIRE_SIZE`. Holds for
    every decompressor (snappy enters the reader as a parameter), so
    under-allocation is impossible by theorem.
-/

import LeanSpec.Networking.ReqResp

namespace LeanSpec.Networking

/-- Number of bytes `encode_varint` emits for `n` (`varint.py`): one
byte per 7-bit group, at least one. -/
def varintSize (n : Nat) : Nat :=
  if n < 128 then 1 else 1 + varintSize (n / 128)
  decreasing_by
    exact Nat.div_lt_self (Nat.lt_of_lt_of_le (by omega) (Nat.le_of_not_lt ‹¬n < 128›)) (by omega)

/-- A value below `128 ^ k` encodes in at most `k` varint bytes. -/
theorem varintSize_le_of_lt_pow :
    ∀ (k n : Nat), 0 < k → n < 128 ^ k → varintSize n ≤ k
  | 1, n, _, hlt => by
    unfold varintSize
    rw [if_pos (by simpa using hlt)]
    omega
  | k + 2, n, _, hlt => by
    unfold varintSize
    by_cases hn : n < 128
    · rw [if_pos hn]; omega
    · rw [if_neg hn]
      have hdiv : n / 128 < 128 ^ (k + 1) := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        calc n < 128 ^ (k + 2) := hlt
        _ = 128 ^ (k + 1) * 128 := by rw [Nat.pow_succ]
      have := varintSize_le_of_lt_pow (k + 1) (n / 128) (by omega) hdiv
      omega

/-- Worst-case wire size of an accepted compressed payload: snappy's
maximum expansion (`n + n/6 + 1024`) of a payload at the
`MAX_PAYLOAD_SIZE` gate. The reader rejects anything larger before
buffering (`compressed_size_bound`). -/
def MAX_COMPRESSED_PAYLOAD_SIZE : Nat :=
  MAX_PAYLOAD_SIZE + MAX_PAYLOAD_SIZE / 6 + 1024

/-- Closed form: 10 MiB + 10 MiB / 6 + 1024. -/
theorem max_compressed_payload_size_eq :
    MAX_COMPRESSED_PAYLOAD_SIZE = 12234410 := by rfl

/-- Worst-case length-prefix size: the LEB128 varint of any declared
length the reader can accept (`≤ MAX_PAYLOAD_SIZE < 128^4`). -/
def MAX_LENGTH_PREFIX_SIZE : Nat := 4

/-- An in-bound declared length encodes in at most
`MAX_LENGTH_PREFIX_SIZE` varint bytes. -/
theorem varintSize_le_prefix_bound {n : Nat} (h : n ≤ MAX_PAYLOAD_SIZE) :
    varintSize n ≤ MAX_LENGTH_PREFIX_SIZE := by
  have hmax : MAX_PAYLOAD_SIZE = 10485760 := rfl
  have hpow : (128 : Nat) ^ 4 = 268435456 := by rfl
  exact varintSize_le_of_lt_pow 4 n (by omega) (by omega)

/-- Total wire allocation one accepted request can require: length
prefix plus worst-case compressed payload. This is the preallocation
constant the upstream proposal names — 12 234 414 bytes per req/resp
stream. -/
def MAX_REQUEST_WIRE_SIZE : Nat :=
  MAX_LENGTH_PREFIX_SIZE + MAX_COMPRESSED_PAYLOAD_SIZE

/-- Closed form of the preallocation constant. -/
theorem max_request_wire_size_eq : MAX_REQUEST_WIRE_SIZE = 12234414 := by
  rfl

/-- #70: for any request the reader accepts, the whole wire footprint —
varint length prefix plus compressed payload — fits in
`MAX_REQUEST_WIRE_SIZE`. A conforming client may preallocate exactly
this much per req/resp stream; under-allocation is impossible by
theorem, for every decompressor. -/
theorem request_wire_bound (decompress : ByteArray → Option ByteArray)
    (declaredLength : Nat) (compressed : ByteArray) (msg : ByteArray)
    (h : readRequest decompress declaredLength compressed = some msg) :
    varintSize declaredLength + compressed.size ≤ MAX_REQUEST_WIRE_SIZE := by
  -- The declared length passed the `MAX_PAYLOAD_SIZE` gate.
  have hdecl : declaredLength ≤ MAX_PAYLOAD_SIZE := by
    unfold readRequest at h
    split at h
    · simp at h
    · next hgate => exact Nat.le_of_not_lt hgate
  have hprefix := varintSize_le_prefix_bound hdecl
  have hwire := compressed_size_bound decompress declaredLength
    compressed msg h
  have hf : MAX_LENGTH_PREFIX_SIZE = 4 := rfl
  unfold MAX_REQUEST_WIRE_SIZE MAX_COMPRESSED_PAYLOAD_SIZE
  omega

end LeanSpec.Networking
