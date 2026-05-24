/-
  C3: Lyapunov Radius of Validity -- definitions

  This file keeps the linear-algebra inputs as explicit real inequalities.
  The later files prove the radius-of-validity algebra from those inputs.
-/
import Mathlib

noncomputable section

namespace TINProofs.C3

/-- Scalar data used by the Lyapunov radius estimate. -/
structure LyapunovSetup where
  alphaMin : ℝ
  alphaMax : ℝ
  q : ℝ
  r0 : ℝ
  opNormA : ℝ
  M : ℝ
  hAlphaMin_pos : 0 < alphaMin
  hAlphaMax_pos : 0 < alphaMax
  hq_pos : 0 < q
  hr0_pos : 0 < r0
  hOpNormA_pos : 0 < opNormA
  hM_pos : 0 < M

/-- Critical radius `r* = min(r0, q / (2 ||A|| M))`. -/
def criticalRadius (S : LyapunovSetup) : ℝ :=
  min S.r0 (S.q / (2 * S.opNormA * S.M))

/-- Exponential decay rate in the Lyapunov estimate. -/
def lyapunovDecayRate (S : LyapunovSetup) : ℝ :=
  S.q / (2 * S.alphaMax)

/--
Pointwise scalar facts for one perturbation.

`rho` is `‖delta‖`, `V` is the quadratic Lyapunov value, `quad` is
`delta^T Q delta`, and `remainder` is `2 delta^T A R(delta)`.
-/
structure LyapunovPoint (S : LyapunovSetup) where
  rho : ℝ
  V : ℝ
  Vdot : ℝ
  quad : ℝ
  remainder : ℝ
  hrho_nonneg : 0 ≤ rho
  eigenSandwich : S.alphaMin * rho ^ 2 ≤ V ∧ V ≤ S.alphaMax * rho ^ 2
  vdotDecomp : Vdot = -quad + remainder
  quadLower : S.q * rho ^ 2 ≤ quad
  remainderAbsBound : |remainder| ≤ S.opNormA * S.M * rho ^ 3

end TINProofs.C3

end
