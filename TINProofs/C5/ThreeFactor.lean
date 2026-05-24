/-
  C5 Proposition 2.7: exact three-factor sparse law.
-/
import TINProofs.C5.Defs

open MeasureTheory Real

noncomputable section

namespace TINProofs.C5

/-- The three-factor sparse law: `DR = S_T * exp(E[H] * lambda) * Phi`. -/
theorem three_factor (s : SparseLawSetup) :
    s.DR = s.S_T * s.etaLyap * s.Phi := by
  have hpos : 0 < s.etaLyap := by
    unfold SparseLawSetup.etaLyap
    exact Real.exp_pos _
  have heta : s.eta = s.etaLyap * s.Phi := by
    unfold SparseLawSetup.Phi
    exact (mul_div_cancel₀ s.eta (ne_of_gt hpos)).symm
  rw [s.hDR, heta, mul_assoc]

end TINProofs.C5

end
