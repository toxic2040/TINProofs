# Blueprint C5: Three-Factor Sparse Law Decomposition (Proposition 2.7)

Source: `~/Desktop/Papers/papers/monograph_factorization_body.tex`, lines 448-559
Also: `~/Desktop/Papers/papers/classification_theorem.tex`, lines 392-416

## Goal

Formalize the three-factor decomposition:

    DR = S_T * exp(E[H] * lambda) * Phi

This builds on C4's `TemporalTransport` and its two-factor factorization
DR = S_T * eta. The three-factor form refines eta into channel attenuation
(exp(E[H] * lambda)) and routing distortion (Phi).

---

## Mathematical Content

The decomposition is a change of variables, not an approximation.

Given:
- eta = DR / S_T (from C4, conditional delivery probability)
- E[H] = expected hop count along oracle paths
- lambda = E[log p_h] = Lyapunov exponent (per-hop log-attenuation)
- eta_lyap = exp(E[H] * lambda) = chain attenuation factor

Define:
- Phi = eta / eta_lyap (routing distortion / morphology residual)

Then:
- DR = S_T * eta = S_T * eta_lyap * Phi = S_T * exp(E[H] * lambda) * Phi

The factorization is exact because Phi is defined as the ratio.

### What makes this more than a definition

1. The decomposition separates three independently measurable quantities
2. lambda < 0 when all per-hop probabilities p_h < 1 (from ln properties)
3. 0 < eta_lyap < 1 when lambda < 0 and E[H] > 0 (chain attenuation is proper)
4. Phi = 1 exactly when the renewal prediction matches simulation
5. sign(ln Phi) determines trap vs cluster classification

---

## Formalization Strategy

### Two layers

**Layer A: The algebraic identity (the theorem)**
- Import C4's TemporalTransport, DR, ST, eta
- Define chain attenuation and Phi as scalar quantities
- Prove the three-factor identity from C4's two-factor identity
- Prove basic properties of the factors

**Layer B: Properties of the Lyapunov exponent (supporting lemmas)**
- lambda < 0 when all p_h in (0,1)
- exp(E_H * lambda) in (0,1) when lambda < 0 and E_H > 0
- Phi > 0 when eta > 0 and eta_lyap > 0
- The decomposition is invariant to the choice of oracle (gauge-protected sign)

---

## File Structure

```
TINProofs/
├── C5/
│   ├── Defs.lean            -- SparseLawSetup, chain attenuation, Phi
│   ├── ThreeFactor.lean     -- Main theorem: DR = S_T * eta_lyap * Phi
│   ├── ChainProperties.lean -- lambda < 0, 0 < eta_lyap < 1, Phi > 0
│   └── Classification.lean  -- sign(gamma) determines class (optional)
```

---

## Part 0: Definitions

### Approach: scalar extension of C4

C4 works at the abstract event level (probability spaces). C5 extends
with scalar quantities that characterize the transport channel. We do
NOT need to formalize oracle paths — we take E[H] and lambda as given
scalar parameters, just as C3 took eigenvalues as given.

```lean
import TINProofs.C4.Factorization

open MeasureTheory Real

noncomputable section

namespace TINProofs.C5

/-- Scalar parameters for the three-factor sparse law. -/
structure SparseLawSetup where
  S_T : ℝ       -- temporal reachability, in (0, 1]
  eta : ℝ       -- transport efficiency, in [0, 1]
  E_H : ℝ       -- expected oracle hop count, > 0
  lyap : ℝ      -- Lyapunov exponent = E[log p_h], < 0
  hST_pos : 0 < S_T
  hST_le : S_T ≤ 1
  heta_nonneg : 0 ≤ eta
  heta_le : eta ≤ 1
  hEH_pos : 0 < E_H
  hlyap_neg : lyap < 0
  -- The two-factor identity holds:
  DR : ℝ
  hDR : DR = S_T * eta

/-- Chain attenuation factor: exp(E[H] * lambda). -/
def SparseLawSetup.etaLyap (s : SparseLawSetup) : ℝ :=
  Real.exp (s.E_H * s.lyap)

/-- Routing distortion (morphology residual): Phi = eta / eta_lyap. -/
def SparseLawSetup.Phi (s : SparseLawSetup) : ℝ :=
  s.eta / s.etaLyap

end TINProofs.C5
```

### Alternative: connect to C4's TemporalTransport

If you want the three-factor theorem to directly reference C4's types:

```lean
/-- Extension of a TemporalTransport with hop count and Lyapunov data. -/
structure SparseLawExtension {Ω : Type*} [MeasurableSpace Ω]
    (tt : TINProofs.C4.TemporalTransport Ω) where
  E_H : ℝ
  lyap : ℝ
  hEH_pos : 0 < E_H
  hlyap_neg : lyap < 0
```

**Recommendation:** Start with the scalar approach. It's faster, cleaner,
and captures the mathematical content. Add the TemporalTransport connection
later if desired.

---

## Part 1: Three-Factor Identity (main theorem)

```lean
/-- The three-factor sparse law: DR = S_T * exp(E[H] * lambda) * Phi. -/
theorem three_factor (s : SparseLawSetup) :
    s.DR = s.S_T * s.etaLyap * s.Phi := by
  -- DR = S_T * eta  (hypothesis hDR)
  -- eta = etaLyap * Phi  (definition of Phi, when etaLyap ≠ 0)
  -- Therefore DR = S_T * etaLyap * Phi
  sorry
```

**Proof strategy:**
1. `s.DR = s.S_T * s.eta` (from `s.hDR`)
2. `s.eta = s.etaLyap * s.Phi` (from definition of Phi = eta / etaLyap,
   provided etaLyap ≠ 0)
3. Substitute into step 1

The key step is showing etaLyap ≠ 0 so that eta = etaLyap * (eta / etaLyap).
Since etaLyap = exp(E_H * lyap) and exp is always positive, etaLyap > 0.

```lean
theorem etaLyap_pos (s : SparseLawSetup) : 0 < s.etaLyap := by
  unfold SparseLawSetup.etaLyap
  exact Real.exp_pos _
```

Then:
```lean
theorem eta_eq_etaLyap_mul_phi (s : SparseLawSetup) :
    s.eta = s.etaLyap * s.Phi := by
  unfold SparseLawSetup.Phi
  rw [mul_div_cancel₀ s.eta (ne_of_gt (etaLyap_pos s))]
```

And the main theorem:
```lean
theorem three_factor (s : SparseLawSetup) :
    s.DR = s.S_T * s.etaLyap * s.Phi := by
  rw [s.hDR, mul_assoc, ← eta_eq_etaLyap_mul_phi s]
```

This should be very short — the whole thing is `rw` and `mul_assoc`.

Mathlib:
- `Real.exp_pos` : 0 < exp x for all x
- `mul_div_cancel₀` : a = b * (a / b) when b ≠ 0
- `mul_assoc` : (a * b) * c = a * (b * c)

---

## Part 2: Chain Attenuation Properties

### 2a. Lyapunov exponent is negative

This is a hypothesis in SparseLawSetup, but we can also prove it from
per-hop probabilities as a standalone lemma:

```lean
/-- The mean of log(p_h) is negative when all p_h are in (0, 1). -/
theorem lyapunov_exponent_neg {n : ℕ} (ps : Fin n → ℝ)
    (hps_pos : ∀ i, 0 < ps i) (hps_lt : ∀ i, ps i < 1)
    (hn : 0 < n) :
    (∑ i, Real.log (ps i)) / n < 0 := by
  -- Each log(p_i) < 0 since 0 < p_i < 1
  -- Sum of negatives is negative
  -- Dividing by positive n preserves sign
  sorry
```

Mathlib:
- `Real.log_neg` : 0 < x → x < 1 → log x < 0
- `Finset.sum_neg` : sum of negatives is negative
- `div_neg_of_neg_of_pos` : a/b < 0 when a < 0 and b > 0

### 2b. Chain attenuation is in (0, 1)

```lean
/-- Chain attenuation is positive. -/
theorem etaLyap_pos (s : SparseLawSetup) : 0 < s.etaLyap :=
  Real.exp_pos _

/-- Chain attenuation is less than 1 when lambda < 0 and E[H] > 0. -/
theorem etaLyap_lt_one (s : SparseLawSetup) : s.etaLyap < 1 := by
  unfold SparseLawSetup.etaLyap
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith [s.hEH_pos, s.hlyap_neg])
```

Mathlib:
- `Real.exp_pos` : 0 < exp x
- `Real.exp_lt_exp` : exp x < exp y ↔ x < y
- `Real.exp_zero` : exp 0 = 1

### 2c. Phi is positive when eta is positive

```lean
/-- Phi > 0 when eta > 0. -/
theorem phi_pos (s : SparseLawSetup) (heta : 0 < s.eta) : 0 < s.Phi := by
  unfold SparseLawSetup.Phi
  exact div_pos heta (etaLyap_pos s)
```

---

## Part 3: Classification Skeleton (optional, for C1 bridge)

If time permits, add the morphology slope definition:

```lean
/-- Morphology slope: gamma = d(ln Phi) / d(E[H]).
    Positive gamma = cluster class, negative gamma = trap class. -/
def morphologySlope (phi1 phi2 : ℝ) (eh1 eh2 : ℝ)
    (hphi1 : 0 < phi1) (hphi2 : 0 < phi2) (heh : eh1 ≠ eh2) : ℝ :=
  (Real.log phi2 - Real.log phi1) / (eh2 - eh1)
```

And the classification:
```lean
/-- Trap class: gamma < 0 (adding hops makes things worse). -/
def isTrap (gamma : ℝ) : Prop := gamma < 0

/-- Cluster class: gamma > 0 (adding hops improves efficiency). -/
def isCluster (gamma : ℝ) : Prop := 0 < gamma
```

This is purely definitional but sets up the vocabulary for future work.

---

## GPT Workflow

1. **Defs.lean** — Define SparseLawSetup, etaLyap, Phi. Get it compiling.

2. **ThreeFactor.lean** — Prove the main identity. This should be 3-5 lines:
   etaLyap_pos → eta_eq_etaLyap_mul_phi → three_factor via rw + mul_assoc.
   This is the core deliverable.

3. **ChainProperties.lean** — Prove etaLyap_pos, etaLyap_lt_one, phi_pos,
   and the Lyapunov exponent negativity lemma. Uses Real.exp and Real.log
   properties from mathlib.

4. **Classification.lean** (optional) — Morphology slope definition and
   trap/cluster classification. Purely definitional, no proofs needed
   beyond the definitions themselves.

Build after every file. Add imports to TINProofs.lean.

**IMPORTANT: Read TINProofs.lean before editing it — previous sessions
added C2, C3, and C4 imports that must be preserved.**

---

## Success Criteria

- `lake build` passes with zero errors
- Main theorem `three_factor` has no `sorry`
- `etaLyap_pos`, `etaLyap_lt_one`, `phi_pos` have no `sorry`
- Lyapunov exponent negativity from per-hop probabilities: acceptable
  to leave as `sorry` if Finset.sum reasoning is difficult, but should
  be straightforward

Expected total: 4 files, ~100-150 lines, all but possibly one `sorry`-free.

---

## Known Pitfalls

1. **exp/log in Lean**: `Real.exp` and `Real.log` are in `Mathlib.Analysis.SpecialFunctions.ExpDeriv`
   or `Mathlib.Analysis.SpecialFunctions.Log.Basic`. Import `Mathlib` to get everything.

2. **Division by zero**: Phi = eta / etaLyap. Since etaLyap = exp(...) > 0,
   division is safe. But Lean needs to see `ne_of_gt (exp_pos _)` to confirm
   the denominator is nonzero.

3. **mul_div_cancel**: The key identity `a = b * (a / b)` when `b ≠ 0`.
   In mathlib4 this is `mul_div_cancel₀` or `div_mul_cancel₀`. Try both.

4. **Real.exp_zero**: exp(0) = 1. Needed for `etaLyap_lt_one` proof.

5. **nlinarith**: For the inequality `E_H * lyap < 0` from `E_H > 0` and
   `lyap < 0`, use `nlinarith` (nonlinear arithmetic).

---

## What This Unlocks for C1

With the three-factor decomposition formalized, C1 (Commodity Hull Theorem)
can define:
- Per-path action: A_pi(lam_c) = -ln Q_pi + lam_c * T_pi
- This is affine in lam_c for each path
- Support function F(lam_c) = inf_pi A_pi(lam_c)
- Hull structure from the affine family

The connection: E[H] * lambda from C5 is the total action along the oracle
path. Different commodity hazard rates lam_c scan different paths on the
hull. The three-factor form makes this explicit by separating the
path-dependent cost (E[H] * lambda) from the routing-dependent residual (Phi).
