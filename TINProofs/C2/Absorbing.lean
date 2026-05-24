/-
  C2 Part (i): Absorbing Lowest Tier

  This file proves the source-controlled cutoff arithmetic behind the
  absorbing-tier claim. The Binomial median and mode facts are kept as
  explicit hypotheses; the project does not yet define Binomial medians
  or modes as first-class objects.
-/
import TINProofs.C2.Defs

open Finset BigOperators Nat

noncomputable section

/-- The last threshold, corresponding to the boundary above the lowest tier. -/
def TierSystem.lowestThreshold (ts : TierSystem) : Fin (ts.M - 1) :=
  ⟨ts.M - 2, by
    have hM : 2 ≤ ts.M := ts.hM
    omega⟩

/-- If the Binomial mean lies more than one unit below a tier cutoff in real
    coordinates, then its natural ceiling lies strictly below the integer
    cutoff. -/
theorem ceil_mean_lt_xMin_of_lt_sub_one (ts : TierSystem) (i : Fin (ts.M - 1))
    (n : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ i - 1) :
    ⌈(n : ℝ) * p⌉₊ < ts.xMin i := by
  unfold TierSystem.xMin
  rw [Nat.lt_ceil]
  have hmean_nonneg : 0 ≤ (n : ℝ) * p := by
    exact mul_nonneg (by exact_mod_cast Nat.zero_le n) hp
  have hceil : (⌈(n : ℝ) * p⌉₊ : ℝ) < (n : ℝ) * p + 1 :=
    Nat.ceil_lt_add_one hmean_nonneg
  linarith

/-- Non-strict form matching the displayed source inequality. -/
theorem ceil_mean_le_xMin_of_lt_sub_one (ts : TierSystem) (i : Fin (ts.M - 1))
    (n : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ i - 1) :
    ⌈(n : ℝ) * p⌉₊ ≤ ts.xMin i :=
  le_of_lt (ceil_mean_lt_xMin_of_lt_sub_one ts i n p hp h)

/-- Conditional median consequence: once the standard Binomial median upper
    bound is supplied, the median is below the tier cutoff. -/
theorem median_lt_xMin_of_median_le_ceil_mean (ts : TierSystem)
    (i : Fin (ts.M - 1)) (n median : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hmedian : median ≤ ⌈(n : ℝ) * p⌉₊)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ i - 1) :
    median < ts.xMin i :=
  lt_of_le_of_lt hmedian (ceil_mean_lt_xMin_of_lt_sub_one ts i n p hp h)

/-- Conditional mode consequence: if the mode is no larger than such a median,
    then the mode is also below the tier cutoff. -/
theorem mode_lt_xMin_of_mode_le_median (ts : TierSystem)
    (i : Fin (ts.M - 1)) (n mode median : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hmode : mode ≤ median)
    (hmedian : median ≤ ⌈(n : ℝ) * p⌉₊)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ i - 1) :
    mode < ts.xMin i :=
  lt_of_le_of_lt hmode
    (median_lt_xMin_of_median_le_ceil_mean ts i n median p hp hmedian h)

/-- Lowest-tier specialization of the ceiling cutoff bound. -/
theorem absorbing_lowest_tier_ceiling_lt_cutoff (ts : TierSystem)
    (n : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ ts.lowestThreshold - 1) :
    ⌈(n : ℝ) * p⌉₊ < ts.xMin ts.lowestThreshold :=
  ceil_mean_lt_xMin_of_lt_sub_one ts ts.lowestThreshold n p hp h

/-- Lowest-tier specialization with the Binomial median upper bound supplied
    as an explicit hypothesis. -/
theorem absorbing_lowest_tier_median_lt_cutoff (ts : TierSystem)
    (n median : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hmedian : median ≤ ⌈(n : ℝ) * p⌉₊)
    (h : (n : ℝ) * p < (ts.k : ℝ) * ts.τ ts.lowestThreshold - 1) :
    median < ts.xMin ts.lowestThreshold :=
  median_lt_xMin_of_median_le_ceil_mean
    ts ts.lowestThreshold n median p hp hmedian h

end
