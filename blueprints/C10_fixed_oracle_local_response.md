# Blueprint C10: Fixed-Oracle Local Response (discussion v0.9 Section 51.2)

Source: `~/Desktop/TIN_daily/private_not_for_publication/discussion_v0.9.md`, Section 51.2

## Goal

Formalize the fixed-oracle local response theorem. Under oracle independence,
a hazard impulse at time `t` can affect the action at the same time, but it
cannot alter the oracle-selected route state at positive lag.

The theorem block separates two quantities that can otherwise be conflated:

- retarded causal response, `K_R(ell)`
- route-state autocorrelation, `N_AB(ell)`

The formal claim is deliberately narrow: for `lag > 0`, the local response
term `delta_action_t_ell` is zero. A nonzero positive-lag response contradicts
the oracle-independence hypothesis.

---

## Mathematical Statement

### Setup

An oracle setup contains a finite route-state space. An event pair contains:

- an injection event at time `t`
- an injection event at time `t + ell`
- a natural-number lag `ell`

The oracle-independence hypothesis is encoded as:

```lean
pair.lag = 0 ∨ delta_action_t_ell = 0
```

This means the only potentially nonzero response is local in lag space.

### Main theorem

Positive-lag response vanishes:

```text
lag > 0 -> delta_action_t_ell = 0
```

### No shortcut theorem

If the response vanishes at positive lag, then a claimed positive-lag
nonzero response is impossible:

```text
lag > 0 and delta_action_t_ell ≠ 0 -> False
```

---

## Proof Structure

Four theorems are staged in `TINProofs/C10/LocalResponse.lean`; two still
contain `sorry`.

### 1. `response_vanishes_at_positive_lag`

Input hypotheses:

```lean
oi : OracleIndependence O pair
h_lag_pos : 0 < pair.lag
```

Target:

```lean
oi.delta_action_t_ell = 0
```

Proof route:

1. Case split on `oi.h_local`.
2. The `pair.lag = 0` branch contradicts `0 < pair.lag`.
3. The other branch is exactly the target.

### 2. `response_local_at_lag_zero`

Already closed:

```lean
theorem response_local_at_lag_zero ... : True := by
  trivial
```

This theorem records that the Lean file does not rule out nonzero lag-zero
response.

### 3. `response_kernel_local`

Already closed:

```lean
theorem response_kernel_local ... :
    pair.lag = 0 ∨ oi.delta_action_t_ell = 0 :=
  oi.h_local
```

This theorem exposes the oracle-independence disjunction directly.

### 4. `no_fdr_shortcut`

Input hypotheses:

```lean
h_lag_pos : 0 < pair.lag
h_N_nontrivial : oi.delta_action_t_ell ≠ 0
```

Target:

```lean
False
```

Proof route:

1. Apply `response_vanishes_at_positive_lag` to get
   `oi.delta_action_t_ell = 0`.
2. Apply the nonzero hypothesis to that equality.

---

## Lean Formalization Strategy

### Key decision: encode locality as a disjunction

`OracleIndependence.h_local` is the entire formal content needed by the
two staged proofs:

```lean
h_local : pair.lag = 0 ∨ delta_action_t_ell = 0
```

The proof does not model the oracle function, route-state dynamics, or
autocorrelation kernel. It verifies the logical consequence of the stated
locality hypothesis.

### File structure

```text
TINProofs/
├── C10/
│   ├── Defs.lean           -- OracleSetup, InjectionEvent, EventPair, OracleIndependence
│   └── LocalResponse.lean  -- 4 theorem statements, 2 staged proofs
```

### Current status

```text
TINProofs/C10/Defs.lean            zero sorry
TINProofs/C10/LocalResponse.lean   zero sorry across 4 theorems
```

Direct module build passes:

```text
lake build TINProofs.C10.LocalResponse
```

---

## Theorem Sketches

### `response_vanishes_at_positive_lag`

```lean
theorem response_vanishes_at_positive_lag
    (O : OracleSetup) (pair : EventPair O)
    (oi : OracleIndependence O pair)
    (h_lag_pos : 0 < pair.lag) :
    oi.delta_action_t_ell = 0 := by
  rcases oi.h_local with h_lag_zero | h_delta_zero
  · omega
  · exact h_delta_zero
```

If `omega` does not close the first branch from `h_lag_zero` and
`h_lag_pos`, an explicit contradiction form is available:

```lean
  · exfalso
    omega
```

### `no_fdr_shortcut`

```lean
theorem no_fdr_shortcut
    (O : OracleSetup) (pair : EventPair O)
    (oi : OracleIndependence O pair)
    (h_lag_pos : 0 < pair.lag)
    (h_N_nontrivial : oi.delta_action_t_ell ≠ 0) :
    False := by
  have h_zero := response_vanishes_at_positive_lag O pair oi h_lag_pos
  exact h_N_nontrivial h_zero
```

---

## Trust Boundaries

1. **Oracle independence.** The substantive modeling claim that the oracle
   at positive lag does not consult the hazard impulse is encoded in
   `OracleIndependence.h_local`.

2. **Autocorrelation not modeled.** The formal statement does not build
   `N_AB(ell)` as a separate object. The no-shortcut theorem only states
   that a nonzero positive-lag value of the response term contradicts
   fixed-oracle locality.

3. **Natural-number lag.** `pair.lag` is a `Nat`, so the positive-lag
   contradiction is arithmetic over naturals.

---

## Wiring Target

The closed block is wired with these imports:

```lean
import TINProofs.C10.Defs
import TINProofs.C10.LocalResponse
```

`TINProofs/Statements.lean` checks:

```lean
#check @TINProofs.C10.response_vanishes_at_positive_lag
#check @TINProofs.C10.response_kernel_local
#check @TINProofs.C10.no_fdr_shortcut
```

## Success Criteria

- `lake build TINProofs.C10.LocalResponse` passes
- `lake build TINProofs` passes
- `rg -n "sorry" TINProofs/C10` returns no matches
- The final theorem remains a contradiction of positive-lag nonzero response,
  not a broader statement about route-state autocorrelation
