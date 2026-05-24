# Blueprint C2: Stochastic Certification Asymmetry (Theorem S2)

Source: `~/Desktop/Papers/sdtc/stochastic_certification.tex`, lines 108-225

## Goal

Formalize and machine-verify Theorem S2 from the stochastic certification
paper. Five parts, increasing difficulty. No domain-specific infrastructure
needed -- pure probability and combinatorics over Binomial/Poisson.

---

## Part 0: Definitions (formalize first, no proofs needed)

### Tier mapping

```
Given:
  k : ℕ+              -- reserve cycles (bundles per window)
  M : ℕ, M ≥ 2        -- number of tiers
  τ : Fin (M-1) → ℝ   -- thresholds, strictly decreasing, all in (0,1)

Define:
  DR(X) := min(X/k, 1)                     -- delivery ratio
  x(i)  := ⌈k * τ(i)⌉                     -- min integer X achieving tier i
  tier(X) := largest i such that X ≥ x(i)  -- tier classification
```

### Lean type sketch

```lean
import Mathlib

structure TierSystem where
  k : ℕ+
  M : ℕ
  hM : 2 ≤ M
  τ : Fin (M - 1) → ℝ
  hτ_pos : ∀ i, 0 < τ i
  hτ_lt_one : ∀ i, τ i < 1
  hτ_strict_anti : StrictAnti τ

noncomputable def TierSystem.DR (ts : TierSystem) (X : ℕ) : ℝ :=
  min ((X : ℝ) / (ts.k : ℝ)) 1

noncomputable def TierSystem.x_min (ts : TierSystem) (i : Fin (ts.M - 1)) : ℕ :=
  Nat.ceil (ts.k * ts.τ i)
```

### Mathlib modules to import

Search for these in current mathlib4 -- names may have shifted:

- `Mathlib.Probability.ProbabilityMassFunction.Basic` -- PMF type
- `Mathlib.Probability.Distributions.Binomial` -- if it exists; otherwise
  define Binomial PMF manually as `PMF.ofFinset` over `Finset.range (n+1)`
  with mass `C(n,k) * p^k * (1-p)^(n-k)`
- `Mathlib.Analysis.SpecificLimits.Basic` -- for Poisson limit
- `Mathlib.Order.Filter.Basic` -- for tendsto / limits
- `Mathlib.Data.Nat.Ceil` -- Nat.ceil, Nat.floor
- `Mathlib.Data.Real.Basic` -- ℝ arithmetic

**If Binomial PMF is not in mathlib:** Define it manually. This is fine --
the definition is straightforward and the proof doesn't depend on a deep
library implementation. What matters is that we can state and prove
properties about Binomial CDF tails.

---

## Part (v): Gap Tiers -- START HERE (easiest)

**Statement:** Tier T is unreachable when ⌈k·τ_T⌉ = ⌈k·τ_{T-1}⌉.

**Why start here:** Pure integer arithmetic. No probability theory needed.
Builds familiarity with the TierSystem type before harder parts.

**Proof strategy:**
1. The achievable DR values are {0, 1/k, 2/k, ..., 1}.
2. Tier T requires DR ∈ [τ_T, τ_{T-1}).
3. An integer X achieves DR = X/k ∈ [τ_T, τ_{T-1}) iff ⌈k·τ_T⌉ ≤ X < ⌈k·τ_{T-1}⌉.
4. When ⌈k·τ_T⌉ = ⌈k·τ_{T-1}⌉, no such X exists.

**Lean statement sketch:**

```lean
theorem gap_tier (ts : TierSystem)
    (T : Fin (ts.M - 1))
    (T_pred : Fin (ts.M - 1))
    (hT : T_pred.val + 1 = T.val)  -- T_pred is the tier above T
    (h_gap : ts.x_min T = ts.x_min T_pred) :
    ∀ X : ℕ, ¬(ts.x_min T ≤ X ∧ X < ts.x_min T_pred) := by
  intro X ⟨h1, h2⟩
  omega  -- should close from h_gap, h1, h2
```

**Key mathlib lemmas:**
- `Nat.ceil_le` : ⌈x⌉ ≤ n ↔ x ≤ n
- `Nat.le_ceil` : x ≤ ⌈x⌉
- `omega` tactic should handle the integer contradiction directly

---

## Part (ii): Asymmetry Ratio -- SECOND (definition + simple CDF)

**Statement:** R_T = P(X ≤ x_T - 1) / P(X ≥ x_{T-1}) is an exact function
of (n, p, k, {τ_i}).

**Proof strategy:** This is really a definition plus the observation that
both numerator and denominator are finite sums of Binomial PMF values,
hence exact closed-form expressions in (n, p). "No fitted parameters"
means the ratio is determined by the inputs alone.

**Lean approach:**
1. Define Binomial CDF: `binomial_cdf n p m := ∑ i in Finset.range (m+1), binomial_pmf n p i`
2. Define R_T using CDF values
3. Show both numerator and denominator are determined by (n, p, k, τ)

```lean
noncomputable def binomial_pmf (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose n k) * p ^ k * (1 - p) ^ (n - k)

noncomputable def R_T (ts : TierSystem) (n : ℕ) (p : ℝ)
    (T : Fin (ts.M - 1)) (T_pred : Fin (ts.M - 1)) : ℝ :=
  (∑ i in Finset.range (ts.x_min T), binomial_pmf n p i) /
  (∑ i in Finset.Icc (ts.x_min T_pred) n, binomial_pmf n p i)
```

**This part is mostly definitional.** The "theorem" is that R_T is
well-defined and computable from the given parameters, which follows
from the definition itself. The interesting content is in parts (i)
and (iii) which use R_T.

---

## Part (i): Absorbing Lowest Tier -- THIRD (needs Binomial median)

**Statement:** When np < k·τ_{M-1}, the stochastic mode tier equals the
deterministic tier. Specifically, med(X) ≤ ⌈np⌉ ≤ x_{M-1}.

**Proof strategy:**
1. Use the Binomial median bound: ⌊np⌋ ≤ med(X) ≤ ⌈np⌉
2. When np < k·τ_{M-1} - 1: ⌈np⌉ < ⌈k·τ_{M-1}⌉ = x_{M-1}
3. Therefore med(X) < x_{M-1}, so the median is in the Fail region
4. Since the Binomial is unimodal, mode ≤ median (when median < mean)
   means the mode is also in Fail

**Key lemma needed (may not be in mathlib):**

```lean
-- Binomial median bound (Kaas-Buhrman 1980)
lemma binomial_median_bound (n : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    ⌊n * p⌋ ≤ median (binomial n p) ∧ median (binomial n p) ≤ ⌈n * p⌉ := by
  sorry  -- this is a known result but likely needs to be proved from scratch
```

**If the median bound is hard to formalize:** An alternative is to prove
the weaker statement using Markov's inequality:
  P(X ≥ x_{M-1}) ≤ E[X] / x_{M-1} = np / x_{M-1} < 1/2
which implies med(X) < x_{M-1}. This is easier but gives a weaker bound.

**Mathlib lemmas:**
- `Nat.ceil_lt_add_one` or `Nat.ceil_mono`
- `Nat.floor_le` : ⌊x⌋ ≤ x for x ≥ 0
- Markov's inequality if available in `Mathlib.Probability.Markov`

---

## Part (iii): Poisson Limit -- FOURTH (convergence in distribution)

**Statement:** R_T crosses unity at p*(n,k) → λ*/n as n → ∞, where λ*
solves P(Poisson(λ) ≤ k-2) = P(Poisson(λ) ≥ k).

**Proof strategy:**
1. Binomial(n, λ/n) → Poisson(λ) as n → ∞ (law of small numbers)
2. The crossover condition R_T = 1 becomes a Poisson CDF equation
3. The specific equation is the Poisson median condition

**Key dependency:** Binomial-to-Poisson convergence. Search mathlib for:
- `MeasureTheory.Measure.tendsto_poisson_of_binomial`
- `ProbabilityTheory.binomial_convergence_poisson`
- Or in `Mathlib.Probability.Distributions`

**If not in mathlib:** This is a substantial formalization on its own.
The proof involves showing pointwise convergence of PMF values:
  C(n,k) * (λ/n)^k * (1-λ/n)^(n-k) → e^{-λ} * λ^k / k!
using `(1 - λ/n)^n → e^{-λ}` (which IS in mathlib as
`Real.tendsto_pow_mul_div_factorial_atTop` or similar).

**Lean statement sketch:**

```lean
-- The Poisson crossover condition
noncomputable def poisson_crossover_condition (k : ℕ+) (λ : ℝ) : Prop :=
  (∑ i in Finset.range (k - 1), poisson_pmf λ i) =
  (∑ i in Finset.Ici k, poisson_pmf λ i)

-- This asserts the crossover λ* exists and is unique
theorem poisson_crossover_exists (k : ℕ+) (hk : 2 ≤ k) :
    ∃! λ : ℝ, 0 < λ ∧ poisson_crossover_condition k λ := by
  sorry  -- intermediate value theorem + monotonicity of Poisson CDF in λ
```

---

## Part (iv): Asymptotic Expansion -- FIFTH (hardest)

**Statement:** DR* = λ*/k = 1 - 5/(6k) + O(1/k²).

**Proof strategy:** Uses the Adell-Jodra (2005) result that the Poisson
median lies in [λ - ln 2, λ + 1/3]. The crossover condition places λ*
at the symmetric point of this band.

**This part is the hardest to formalize** because:
1. The Adell-Jodra bound is a published result (2005) not in mathlib
2. The asymptotic expansion requires careful error term tracking
3. O(1/k²) needs formalization as Asymptotics.IsBigO

**Recommendation for GPT:** Attempt parts (v), (ii), (i), (iii) first.
Part (iv) may need to be left as `sorry` initially, or proved only for
specific small values of k as a sanity check.

**If attempting:** The key mathlib module is `Mathlib.Analysis.Asymptotics`
for `IsBigO` and `IsLittleO`. The expansion itself is:
  λ* = k - 1 + 1/6 + O(1/k)
  λ*/k = 1 - 1/k + 1/(6k) + O(1/k²) = 1 - 5/(6k) + O(1/k²)

---

## File Structure

```
TINProofs/
├── TINProofs/
│   └── C2/
│       ├── Defs.lean          -- TierSystem, binomial_pmf, DR, x_min
│       ├── BinomialBasic.lean -- binomial PMF properties, CDF, sum-to-one
│       ├── GapTiers.lean      -- Part (v)
│       ├── AsymmetryRatio.lean -- Part (ii)
│       ├── Absorbing.lean     -- Part (i)
│       ├── PoissonLimit.lean  -- Part (iii)
│       └── Expansion.lean     -- Part (iv)
```

## Suggested GPT Workflow

1. Create `Defs.lean` with all type definitions. Get it to compile.
2. Create `GapTiers.lean` importing Defs. Prove Part (v). This is the
   warmup -- if this doesn't compile, the types need fixing.
3. Create `BinomialBasic.lean` with PMF definition and basic properties
   (non-negative, sums to 1). These lemmas are reused by all other parts.
4. Create `AsymmetryRatio.lean` for Part (ii).
5. Create `Absorbing.lean` for Part (i). This is the first part that
   requires real probability reasoning.
6. Create `PoissonLimit.lean` for Part (iii). This is the hardest
   infrastructure piece.
7. Create `Expansion.lean` for Part (iv). May require `sorry` on the
   Adell-Jodra bound.

## Success Criteria

- `lake build` passes with zero errors
- Parts (v), (ii), (i) have no `sorry`
- Part (iii) has at most one `sorry` (for Binomial→Poisson convergence,
  if not in mathlib)
- Part (iv) may use `sorry` for the Adell-Jodra bound

## Known Pitfalls

1. **Nat vs Real coercion**: Lean is strict about ℕ → ℝ coercion. Use
   `(k : ℝ)` explicitly. The `push_cast` and `norm_cast` tactics help.

2. **Division by zero**: In Lean 4, `n / 0 = 0` for naturals and reals.
   This is fine for our purposes but watch for `k > 0` hypotheses.

3. **Finset.sum vs tsum**: For finite sums (Binomial PMF), use
   `Finset.sum`. For Poisson (infinite support), may need `tsum` with
   summability proofs.

4. **noncomputable**: Most definitions involving ℝ will need the
   `noncomputable` keyword. This is normal and expected.

5. **Decidability**: Classical logic is fine. Use `open Classical` at
   the top of files if needed.

6. **mathlib search**: Use `exact?`, `apply?`, `rw?` tactics liberally
   to find the right lemma names. They are the most valuable tools for
   navigating mathlib.
