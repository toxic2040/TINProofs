/-
  C6: Ahlfors Covering and Volume Scaling -- definitions

  Scalar data encoding Ahlfors gamma-regularity on a finite region.
  The later files prove covering-number bounds from these inputs.
-/
import Mathlib

noncomputable section

namespace TINProofs.C6

/-- Scalar data for the Ahlfors covering theorem. -/
structure AhlforsSetup where
  gamma : ℝ
  C1 : ℝ
  C2 : ℝ
  cardU : ℕ
  hgamma_pos : 0 < gamma
  hC1_pos : 0 < C1
  hC2_pos : 0 < C2
  hC1_le_C2 : C1 ≤ C2
  hcardU_pos : 0 < cardU

/-- Lower bound constant A1 = 1/C2. -/
def lowerConst (S : AhlforsSetup) : ℝ := 1 / S.C2

/-- Upper bound constant A2 = 2^gamma / C1. -/
def upperConst (S : AhlforsSetup) : ℝ := (2 : ℝ) ^ S.gamma / S.C1

theorem lowerConst_pos (S : AhlforsSetup) : 0 < lowerConst S := by
  unfold lowerConst
  exact div_pos one_pos S.hC2_pos

theorem upperConst_pos (S : AhlforsSetup) : 0 < upperConst S := by
  unfold upperConst
  apply div_pos
  · exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) S.gamma
  · exact S.hC1_pos

theorem cardU_cast_pos (S : AhlforsSetup) : (0 : ℝ) < (S.cardU : ℝ) := by
  exact Nat.cast_pos.mpr S.hcardU_pos

end TINProofs.C6

end
