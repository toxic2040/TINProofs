/-
  C6 Lemma 1: covering implies lower bound on covering number.

  If N balls of radius epsilon cover U, and each ball captures at most
  C2 * epsilon^gamma points, then N >= (1/C2) * |U| * epsilon^{-gamma}.
-/
import TINProofs.C6.Defs

noncomputable section

namespace TINProofs.C6

/--
A covering of U by N balls of radius epsilon, where each ball captures
at most C2 * epsilon^gamma points from U (Ahlfors upper regularity).
-/
structure CoveringWitness (S : AhlforsSetup) where
  N : ℕ
  epsilon : ℝ
  heps_pos : 0 < epsilon
  hN_pos : 0 < N
  h_cover : (S.cardU : ℝ) ≤ (N : ℝ) * S.C2 * epsilon ^ S.gamma

/--
Lower bound on covering number from Ahlfors upper regularity.

From |U| <= N * C2 * eps^gamma, rearranging:
  N >= |U| / (C2 * eps^gamma) = (1/C2) * |U| * eps^{-gamma}.
-/
theorem covering_lower_bound (S : AhlforsSetup) (cov : CoveringWitness S) :
    lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) ≤ (cov.N : ℝ) := by
  have hepspow_pos : 0 < cov.epsilon ^ S.gamma :=
    Real.rpow_pos_of_pos cov.heps_pos S.gamma
  have hden_pos : 0 < S.C2 * cov.epsilon ^ S.gamma :=
    mul_pos S.hC2_pos hepspow_pos
  have hdiv : (S.cardU : ℝ) / (S.C2 * cov.epsilon ^ S.gamma) ≤ (cov.N : ℝ) := by
    refine (div_le_iff₀ hden_pos).mpr ?_
    calc
      (S.cardU : ℝ) ≤ (cov.N : ℝ) * S.C2 * cov.epsilon ^ S.gamma := cov.h_cover
      _ = (cov.N : ℝ) * (S.C2 * cov.epsilon ^ S.gamma) := by ring
  calc
    lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma)
        = (S.cardU : ℝ) / (S.C2 * cov.epsilon ^ S.gamma) := by
          unfold lowerConst
          rw [Real.rpow_neg (le_of_lt cov.heps_pos) S.gamma]
          field_simp [ne_of_gt S.hC2_pos, ne_of_gt hepspow_pos]
    _ ≤ (cov.N : ℝ) := hdiv

/--
Equivalent form after multiplying through by eps^gamma.
-/
theorem covering_lower_bound' (S : AhlforsSetup) (cov : CoveringWitness S) :
    lowerConst S * (S.cardU : ℝ) ≤ (cov.N : ℝ) * cov.epsilon ^ S.gamma := by
  have hdiv : (S.cardU : ℝ) / S.C2 ≤ (cov.N : ℝ) * cov.epsilon ^ S.gamma := by
    refine (div_le_iff₀ S.hC2_pos).mpr ?_
    calc
      (S.cardU : ℝ) ≤ (cov.N : ℝ) * S.C2 * cov.epsilon ^ S.gamma := cov.h_cover
      _ = ((cov.N : ℝ) * cov.epsilon ^ S.gamma) * S.C2 := by ring
  calc
    lowerConst S * (S.cardU : ℝ) = (S.cardU : ℝ) / S.C2 := by
      unfold lowerConst
      field_simp [ne_of_gt S.hC2_pos]
    _ ≤ (cov.N : ℝ) * cov.epsilon ^ S.gamma := hdiv

end TINProofs.C6

end
