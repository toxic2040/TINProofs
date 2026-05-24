/-
  C5: Three-factor sparse law -- scalar definitions.
-/
import TINProofs.C4.Factorization

open MeasureTheory Real

noncomputable section

namespace TINProofs.C5

/-- Scalar parameters for the three-factor sparse law. -/
structure SparseLawSetup where
  S_T : ℝ
  eta : ℝ
  E_H : ℝ
  lyap : ℝ
  hST_pos : 0 < S_T
  hST_le : S_T ≤ 1
  heta_nonneg : 0 ≤ eta
  heta_le : eta ≤ 1
  hEH_pos : 0 < E_H
  hlyap_neg : lyap < 0
  DR : ℝ
  hDR : DR = S_T * eta

/-- Chain attenuation factor: `exp(E[H] * lambda)`. -/
def SparseLawSetup.etaLyap (s : SparseLawSetup) : ℝ :=
  Real.exp (s.E_H * s.lyap)

/-- Routing distortion: `Phi = eta / eta_lyap`. -/
def SparseLawSetup.Phi (s : SparseLawSetup) : ℝ :=
  s.eta / s.etaLyap

end TINProofs.C5

end
