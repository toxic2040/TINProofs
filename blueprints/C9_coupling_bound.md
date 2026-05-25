# Blueprint C9: Pinsker Coupling Bound (discussion v0.9 Sections 21.3-21.5)

Source: `~/Desktop/TIN_daily/private_not_for_publication/discussion_v0.9.md`, Sections 21.3-21.5

## Goal

Formalize the scalar coupling bounds for the `S_T * eta` factorization.
The theorem block shows that covariance between infrastructure reachability
and routing efficiency is controlled by either conditional mutual information
or by the two conditional variances.

The current Lean staging keeps probability and information theory at the
trust boundary. Pinsker and Cauchy-Schwarz enter as squared scalar hypotheses;
the verified content is the conversion from those hypotheses to the stated
sqrt bounds and the zero-covariance corollaries.

---

## Mathematical Statement

### Setup

Let:

- `S` be infrastructure reachability, with values in `[0, 1]`
- `eta` be routing efficiency, with values in `[0, 1]`
- `Cov(S, eta | G)` be covariance under coarse information `G`
- `MI(S; eta | G)` be conditional mutual information
- `Var(S | G)` and `Var(eta | G)` be conditional variances

### Main bounds

Pinsker-type coupling bound:

```text
|Cov(S, eta | G)| <= sqrt(2 * MI(S; eta | G))
```

Cauchy-Schwarz variance bound:

```text
|Cov(S, eta | G)| <= sqrt(Var(S | G) * Var(eta | G))
```

### Vanishing cases

Known infrastructure:

```text
Var(S | G) = 0 -> Cov(S, eta | G) = 0
```

Saturated routing:

```text
Var(eta | G) = 0 -> Cov(S, eta | G) = 0
```

Decoupling:

```text
MI(S; eta | G) = 0 -> Cov(S, eta | G) = 0
```

---

## Proof Structure

Five theorems are staged in `TINProofs/C9/CouplingBound.lean`.

### 1. `pinsker_coupling_bound`

Input hypothesis:

```lean
h_pinsker : |C.covSEta| ^ 2 <= 2 * C.mi
```

Target:

```lean
|C.covSEta| <= Real.sqrt (2 * C.mi)
```

Proof route:

1. Prove `0 <= 2 * C.mi` from `C.hmi_nonneg`.
2. Rewrite the goal with `Real.le_sqrt`.
3. Close the squared goal with `h_pinsker`.

### 2. `cauchy_schwarz_coupling_bound`

Input hypothesis:

```lean
h_cs : C.covSEta ^ 2 <= C.varS * C.varEta
```

Target:

```lean
|C.covSEta| <= Real.sqrt (C.varS * C.varEta)
```

Proof route:

1. Prove `0 <= C.varS * C.varEta` from the variance nonnegativity fields.
2. Rewrite the goal with `Real.le_sqrt`.
3. Use `sq_abs` to convert `|cov| ^ 2` to `cov ^ 2`.
4. Close with `h_cs`.

### 3. `coupling_vanishes_known_infrastructure`

Input hypotheses:

```lean
h_cs : C.covSEta ^ 2 <= C.varS * C.varEta
h_varS_zero : C.varS = 0
```

Target:

```lean
C.covSEta = 0
```

Proof route:

1. Rewrite `h_cs` with `h_varS_zero`, reducing the right side to `0`.
2. Combine `h_cs` with `sq_nonneg C.covSEta` to get `C.covSEta ^ 2 = 0`.
3. Apply `sq_eq_zero_iff.mp`.

### 4. `coupling_vanishes_saturated_routing`

Input hypotheses:

```lean
h_cs : C.covSEta ^ 2 <= C.varS * C.varEta
h_varEta_zero : C.varEta = 0
```

Target:

```lean
C.covSEta = 0
```

Proof route:

1. Rewrite `h_cs` with `h_varEta_zero`, reducing the right side to `0`.
2. Combine with `sq_nonneg C.covSEta`.
3. Apply `sq_eq_zero_iff.mp`.

### 5. `decoupling_criterion`

Input hypotheses:

```lean
h_pinsker : |C.covSEta| ^ 2 <= 2 * C.mi
h_mi_zero : C.mi = 0
```

Target:

```lean
C.covSEta = 0
```

Proof route:

1. Rewrite `h_pinsker` with `h_mi_zero`, reducing the right side to `0`.
2. Combine with `sq_nonneg |C.covSEta|`.
3. Get `|C.covSEta| = 0` via `sq_eq_zero_iff.mp`.
4. Apply `abs_eq_zero.mp`.

---

## Lean Formalization Strategy

### Key decision: scalar hypotheses, matching C6-C8

`CouplingSetup` records only the scalar quantities needed by the theorem:
the two values, the covariance, mutual information, variances, and
nonnegativity/range facts. It does not define random variables, sigma-algebras,
or conditional mutual information internally.

This follows the C6-C8 pattern: imported mathematical theorems are represented
as named hypotheses, while Lean checks the algebraic consequences.

### File structure

```text
TINProofs/
├── C9/
│   ├── Defs.lean           -- CouplingSetup
│   └── CouplingBound.lean  -- 5 theorem statements, 5 staged proofs
```

### Current status

```text
TINProofs/C9/Defs.lean            zero sorry
TINProofs/C9/CouplingBound.lean   zero sorry across 5 theorems
```

Direct module build passes:

```text
lake build TINProofs.C9.CouplingBound
```

---

## Theorem Sketches

### `pinsker_coupling_bound`

```lean
theorem pinsker_coupling_bound (C : CouplingSetup)
    (h_pinsker : |C.covSEta| ^ 2 <= 2 * C.mi) :
    |C.covSEta| <= Real.sqrt (2 * C.mi) := by
  have h_rhs_nonneg : 0 <= 2 * C.mi := by
    nlinarith [C.hmi_nonneg]
  rw [Real.le_sqrt (abs_nonneg C.covSEta) h_rhs_nonneg]
  exact h_pinsker
```

### `cauchy_schwarz_coupling_bound`

```lean
theorem cauchy_schwarz_coupling_bound (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 <= C.varS * C.varEta) :
    |C.covSEta| <= Real.sqrt (C.varS * C.varEta) := by
  have h_rhs_nonneg : 0 <= C.varS * C.varEta :=
    mul_nonneg C.hvarS_nonneg C.hvarEta_nonneg
  rw [Real.le_sqrt (abs_nonneg C.covSEta) h_rhs_nonneg]
  simpa [sq_abs] using h_cs
```

### `coupling_vanishes_known_infrastructure`

```lean
theorem coupling_vanishes_known_infrastructure (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 <= C.varS * C.varEta)
    (h_varS_zero : C.varS = 0) :
    C.covSEta = 0 := by
  rw [h_varS_zero, zero_mul] at h_cs
  exact sq_eq_zero_iff.mp (le_antisymm h_cs (sq_nonneg C.covSEta))
```

### `coupling_vanishes_saturated_routing`

```lean
theorem coupling_vanishes_saturated_routing (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 <= C.varS * C.varEta)
    (h_varEta_zero : C.varEta = 0) :
    C.covSEta = 0 := by
  rw [h_varEta_zero, mul_zero] at h_cs
  exact sq_eq_zero_iff.mp (le_antisymm h_cs (sq_nonneg C.covSEta))
```

### `decoupling_criterion`

```lean
theorem decoupling_criterion (C : CouplingSetup)
    (h_pinsker : |C.covSEta| ^ 2 <= 2 * C.mi)
    (h_mi_zero : C.mi = 0) :
    C.covSEta = 0 := by
  rw [h_mi_zero, mul_zero] at h_pinsker
  have h_abs_zero : |C.covSEta| = 0 :=
    sq_eq_zero_iff.mp (le_antisymm h_pinsker (sq_nonneg (|C.covSEta|)))
  exact abs_eq_zero.mp h_abs_zero
```

---

## Trust Boundaries

1. **Pinsker input.** The information-theoretic claim
   `|Cov| ^ 2 <= 2 * MI` is a theorem input, not proved from probability
   measures.

2. **Cauchy-Schwarz input.** The covariance-variance claim
   `Cov ^ 2 <= Var(S) * Var(eta)` is a theorem input.

3. **Scalar model.** `S_val` and `eta_val` are recorded as `[0, 1]` values,
   but the current theorem proofs only need nonnegativity of `mi`, `varS`,
   and `varEta` plus the squared hypotheses.

---

## Wiring Target

The closed block is wired with these imports:

```lean
import TINProofs.C9.Defs
import TINProofs.C9.CouplingBound
```

`TINProofs/Statements.lean` checks:

```lean
#check @TINProofs.C9.pinsker_coupling_bound
#check @TINProofs.C9.cauchy_schwarz_coupling_bound
#check @TINProofs.C9.coupling_vanishes_known_infrastructure
#check @TINProofs.C9.coupling_vanishes_saturated_routing
#check @TINProofs.C9.decoupling_criterion
```

## Success Criteria

- `lake build TINProofs.C9.CouplingBound` passes
- `lake build TINProofs` passes
- `rg -n "sorry" TINProofs/C9` returns no matches
- Trust boundaries remain limited to the Pinsker and Cauchy-Schwarz scalar
  hypotheses
