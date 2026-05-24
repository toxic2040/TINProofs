/-
  C2 Part (ii): Asymmetry Ratio

  The tier asymmetry ratio is the quotient of two finite Binomial sums
  determined by n, p, k, and the tier thresholds.
-/
import TINProofs.C2.Defs

open Finset BigOperators Nat

noncomputable section

/-- Tier cutoffs are positive because k > 0 and every threshold is positive. -/
theorem TierSystem.xMin_pos (ts : TierSystem) (i : Fin (ts.M - 1)) :
    0 < ts.xMin i := by
  unfold TierSystem.xMin
  rw [Nat.ceil_pos]
  exact mul_pos (by exact_mod_cast ts.hk) (ts.hτ_pos i)

/-- For a positive cutoff x, the CDF at x - 1 is the finite lower-tail sum
    over indices 0, ..., x - 1. -/
theorem binomialCDF_pred_eq_sum_range (n : ℕ) (p : ℝ) (x : ℕ) (hx : 0 < x) :
    binomialCDF n p (x - 1) = ∑ j ∈ range x, binomialPMF n p j := by
  unfold binomialCDF
  rw [Nat.sub_one_add_one_eq_of_pos hx]

/-- The tier-specific asymmetry ratio obtained from the two tier cutoffs. -/
def tierAsymmetryRatio (ts : TierSystem) (n : ℕ) (p : ℝ)
    (T Tpred : Fin (ts.M - 1)) : ℝ :=
  asymmetryRatio n p (ts.xMin T) (ts.xMin Tpred)

/-- Part (ii): the asymmetry ratio is exactly the quotient of finite
    Binomial lower-tail and upper-tail sums. -/
theorem tierAsymmetryRatio_eq_binomial_sums (ts : TierSystem) (n : ℕ) (p : ℝ)
    (T Tpred : Fin (ts.M - 1)) :
    tierAsymmetryRatio ts n p T Tpred =
      (∑ j ∈ range (ts.xMin T), binomialPMF n p j) /
        (∑ j ∈ Icc (ts.xMin Tpred) n, binomialPMF n p j) := by
  unfold tierAsymmetryRatio asymmetryRatio binomialUpperTail
  rw [binomialCDF_pred_eq_sum_range n p (ts.xMin T) (ts.xMin_pos T)]

end
