# Blueprint C4: S_T Monotonicity and Braess Localization

Source: `~/Desktop/Papers/papers/monograph_factorization_body.tex`, lines 115-387
Covers: Lemma 2.1, Proposition 2.2, Lemma 2.6, Remark 2.8

## Goal

Formalize:
1. Delivery implies feasibility: D(t) ⊆ F(t)
2. The exact factorization: DR = S_T * eta
3. Monotonicity of S_T under augmentation
4. Braess localization: if DR decreases when adding contacts, eta must decrease

This is the foundational infrastructure for C5 and C1.

---

## Architectural Decision: Abstract Events

We formalize at the **abstract probability level**, not the concrete
temporal graph level. Here's why:

- The mathematical content of these theorems IS the probability relationships
- D ⊆ F, conditional probability, monotonicity under subset — these are
  measure-theoretic facts, not graph-theoretic facts
- mathlib has excellent measure/probability theory but no temporal graph theory
- Building temporal graphs from scratch would take weeks and wouldn't add
  mathematical value to the proofs

We define temporal contact graphs only as opaque types with the properties
we need. The concrete modeling (what a contact IS) stays informal.

---

## Part 1: Definitions

### Core types

```lean
import Mathlib

open MeasureTheory Measure Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- A temporal transport instance: a probability space with delivery and
    feasibility events parametrized by injection time. -/
structure TemporalTransport (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  hprob : IsProbabilityMeasure μ
  D : Set Ω  -- delivery event (bundle is delivered)
  F : Set Ω  -- feasibility event (time-respecting path exists)
  hD : MeasurableSet D
  hF : MeasurableSet F
  h_incl : D ⊆ F  -- Lemma 2.1: delivery implies feasibility
```

### Derived quantities

```lean
/-- Delivery ratio: P(D). -/
noncomputable def TemporalTransport.DR (tt : TemporalTransport Ω) : ℝ≥0∞ :=
  tt.μ tt.D

/-- Temporal reachability: P(F). -/
noncomputable def TemporalTransport.ST (tt : TemporalTransport Ω) : ℝ≥0∞ :=
  tt.μ tt.F

/-- Transport efficiency: P(D | F) = P(D) / P(F).
    (Well-defined when P(F) > 0; equals 0 when P(F) = 0.) -/
noncomputable def TemporalTransport.eta (tt : TemporalTransport Ω) : ℝ≥0∞ :=
  tt.μ tt.D / tt.μ tt.F
```

### Augmentation

```lean
/-- An augmentation of a temporal transport: same probability space,
    feasibility can only increase (more paths available). -/
structure Augmentation (tt tt' : TemporalTransport Ω) where
  h_F_mono : tt.F ⊆ tt'.F  -- augmentation preserves all feasible paths
```

---

## Part 2: Lemma 2.1 — Delivery Implies Feasibility

This is built into the `TemporalTransport` structure as `h_incl : D ⊆ F`.
No separate proof needed — it's an axiom of the model.

But we can state consequences:

```lean
/-- D ⊆ F implies P(D | F^c) = 0. -/
theorem delivery_zero_when_infeasible (tt : TemporalTransport Ω) :
    tt.μ (tt.D ∩ tt.Fᶜ) = 0 := by
  have h : tt.D ∩ tt.Fᶜ = ∅ := by
    ext x; simp; exact fun hD => tt.h_incl hD
  rw [h]; exact measure_empty
```

---

## Part 3: Proposition 2.2 — The Exact Factorization

**Statement:** DR = S_T * eta, i.e., P(D) = P(F) * P(D|F).

This is the law of total probability with D ⊆ F.

```lean
/-- The exact factorization: P(D) = P(F) * P(D) / P(F).
    Equivalently: P(D) = P(F) * eta. -/
theorem exact_factorization (tt : TemporalTransport Ω)
    (hF : tt.μ tt.F ≠ 0) :
    tt.DR = tt.ST * tt.eta := by
  unfold TemporalTransport.DR TemporalTransport.ST TemporalTransport.eta
  rw [ENNReal.mul_div_cancel' hF (measure_ne_top tt.μ tt.F)]
```

**Alternative using real-valued measures:**

If ENNReal division is awkward, work in ℝ≥0 or ℝ:

```lean
/-- Real-valued version. -/
theorem exact_factorization_real (tt : TemporalTransport Ω)
    (hF : (tt.μ tt.F).toReal > 0) :
    (tt.μ tt.D).toReal = (tt.μ tt.F).toReal * ((tt.μ tt.D).toReal / (tt.μ tt.F).toReal) := by
  rw [mul_div_cancel₀]
  exact ne_of_gt hF
```

**Recommended approach:** Try the ENNReal version first. If ENNReal
arithmetic is painful, switch to the real-valued version. Both are
mathematically equivalent.

Mathlib references:
- `ENNReal.mul_div_cancel'` or `ENNReal.div_mul_cancel`
- `MeasureTheory.measure_inter_add_diff` (for D = (D ∩ F) ∪ (D ∩ F^c))
- `Set.subset_inter_iff`

---

## Part 4: Lemma 2.6 — Monotonicity of S_T

**Statement:** If C' augments C, then F(t) ⊆ F'(t), hence S_T ≤ S_T'.

```lean
/-- S_T is monotone under augmentation. -/
theorem st_monotone (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt') :
    tt.ST ≤ tt'.ST := by
  unfold TemporalTransport.ST
  rw [h_same_measure]
  exact measure_mono aug.h_F_mono
```

This is essentially `MeasureTheory.measure_mono` applied to F ⊆ F'.

---

## Part 5: Braess Localization

**Statement:** If adding contacts (augmentation) decreases DR, it must be
because eta decreased. S_T can only increase.

```lean
/-- If DR decreases under augmentation, eta must decrease.
    Equivalently: DR' < DR implies eta' < eta (when S_T, S_T' > 0). -/
theorem braess_in_eta (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt')
    (hF : 0 < (tt.μ tt.F).toReal)
    (hF' : 0 < (tt'.μ tt'.F).toReal)
    (h_dr_decrease : (tt'.μ tt'.D).toReal < (tt.μ tt.D).toReal) :
    (tt'.μ tt'.D).toReal / (tt'.μ tt'.F).toReal <
      (tt.μ tt.D).toReal / (tt.μ tt.F).toReal := by
  -- S_T' >= S_T (monotonicity)
  -- DR' < DR (hypothesis)
  -- eta' = DR'/S_T' <= DR'/S_T < DR/S_T = eta
  sorry  -- outline: div_lt_div using S_T' >= S_T and DR' < DR
```

**Proof sketch for GPT:**
1. From `st_monotone`: S_T' >= S_T, i.e., μ(F') >= μ(F)
2. In real values: (μ F').toReal >= (μ F).toReal
3. eta' = DR'/S_T' and eta = DR/S_T
4. Since DR' < DR and S_T' >= S_T > 0:
   eta' = DR'/S_T' <= DR'/S_T < DR/S_T = eta
5. Use `div_lt_div_of_pos_right` and `div_le_div_of_nonneg_left`

This may need to be broken into two sub-lemmas:
- `div_le_div_of_le_denom` : a/b' ≤ a/b when b ≤ b' and a ≥ 0
- `div_lt_div_of_lt_numer` : a'/b < a/b when a' < a and b > 0

---

## File Structure

```
TINProofs/
├── C4/
│   ├── Defs.lean              -- TemporalTransport, Augmentation, DR, ST, eta
│   ├── Inclusion.lean         -- Lemma 2.1 consequences (D ∩ F^c = ∅)
│   ├── Factorization.lean     -- Proposition 2.2: DR = ST * eta
│   ├── Monotonicity.lean      -- Lemma 2.6: ST monotone under augmentation
│   └── BraessLocalization.lean -- Braess lives in eta
```

## GPT Workflow

### Step 1: Defs.lean

Get the `TemporalTransport` structure compiling. The main challenge is
choosing the right mathlib types.

Key decision: **ENNReal vs Real for measures.**

Option A (ENNReal): `tt.μ tt.D` has type `ℝ≥0∞`. Division and
multiplication work but have special rules (0 * ∞ = 0, etc.).
Pro: no `toReal` conversions. Con: ENNReal arithmetic can be annoying.

Option B (Real): Work with `(tt.μ tt.D).toReal` throughout.
Pro: familiar real arithmetic. Con: need `toReal` conversion lemmas,
and must handle the case where measure is infinite (use
`IsProbabilityMeasure` to guarantee finiteness).

**Recommendation: Start with ENNReal.** Since we have `IsProbabilityMeasure`,
all measures are ≤ 1, so no infinity issues. If ENNReal division is
painful, switch to real.

### Step 2: Inclusion.lean

Should be very short — 1-2 lemmas showing D ∩ F^c = ∅ and P(D ∩ F^c) = 0.
Pure set theory + measure theory.

### Step 3: Factorization.lean

The key lemma. Two approaches:

**Approach A (direct):**
P(D) = P(D ∩ F) + P(D ∩ F^c) = P(D ∩ F) + 0 = P(D ∩ F)
P(D ∩ F) = P(F) * P(D|F) = P(F) * eta

Mathlib: `measure_inter_add_diff`, `measure_mono`, conditional probability
definitions.

**Approach B (by definition):**
eta := P(D) / P(F), so P(D) = P(F) * eta is definitional.
But we need to show P(D) / P(F) is well-defined, i.e., D ⊆ F means
P(D) ≤ P(F).

Search mathlib for:
- `MeasureTheory.Measure.measure_mono` (A ⊆ B → μ A ≤ μ B)
- `ENNReal.mul_div_cancel'`
- `ProbabilityTheory.cond` (conditional probability, if it exists)

### Step 4: Monotonicity.lean

Should be 1 lemma, essentially `measure_mono` applied to F ⊆ F'.
Very short file.

### Step 5: BraessLocalization.lean

The interesting file. Needs careful real-arithmetic reasoning about
ratios. The statement is: if the numerator decreases and the denominator
increases, the ratio decreases.

Key mathlib lemmas:
- `div_lt_div_of_pos_right` or `div_lt_div_right`
- `div_le_div_left` (for the denominator direction)
- `ENNReal.toReal_mono` (for converting measure inequalities to real)

### Success Criteria

- `lake build` passes with zero errors
- Factorization, monotonicity, and inclusion have no `sorry`
- Braess localization: ideally no `sorry`, but the ratio arithmetic may
  need one intermediate `sorry` depending on ENNReal vs Real complications
- All five theorems stated precisely matching the paper

### Known Pitfalls

1. **Measure zero edge case**: When P(F) = 0, eta is undefined (0/0).
   The factorization DR = ST * eta is still "true" in the sense that
   DR = 0 (since D ⊆ F and P(F) = 0 implies P(D) = 0). Handle this
   with an explicit hypothesis `hF : μ F ≠ 0` or prove the degenerate
   case separately.

2. **Same probability space**: The augmentation must be on the SAME
   probability space (same Ω, same μ). This is because we're comparing
   events on the same injection-time distribution, just with different
   contact plans. The structure enforces this.

3. **ENNReal subtleties**: `a / b * b = a` only when `b ≠ 0` and `b ≠ ∞`.
   Use `IsProbabilityMeasure` to get `b ≤ 1 < ∞`.

4. **toReal is not injective on all of ENNReal**: But it is injective on
   [0, ∞), which is guaranteed by finite measures. Use
   `ENNReal.toReal_le_toReal` or `ENNReal.toReal_lt_toReal` with
   finiteness hypotheses.

---

## What This Unlocks (for C5 and C1)

Once these definitions and lemmas compile, C5 (Three-Factor Sparse Law)
can import `TemporalTransport` and add:
- Oracle routing (as a function from injection times to paths)
- Hop count E[H] (expectation over oracle path lengths)
- Lyapunov exponent lambda = E[log p_h]
- The decomposition eta = exp(E[H] * lambda) * Phi

And C1 (Commodity Hull Theorem) can import the path infrastructure and add:
- Path action A_pi(lambda) for multiple paths
- Support function F(lambda) = inf over paths
- Convex hull construction

The abstract event approach in C4 doesn't block these — C5/C1 will
extend with concrete path definitions that sit on top of the abstract
probability framework.
