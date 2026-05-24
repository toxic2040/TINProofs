/-
  C5: sparse-law morphology classification vocabulary.
-/
import TINProofs.C5.ChainProperties

open MeasureTheory Real

noncomputable section

namespace TINProofs.C5

/-- Finite-difference morphology slope for the routing residual. -/
def morphologySlope (phi1 phi2 : ℝ) (eh1 eh2 : ℝ)
    (_hphi1 : 0 < phi1) (_hphi2 : 0 < phi2) (_heh : eh1 ≠ eh2) : ℝ :=
  (Real.log phi2 - Real.log phi1) / (eh2 - eh1)

/-- Trap class: adding hops decreases the residual. -/
def isTrap (gamma : ℝ) : Prop :=
  gamma < 0

/-- Cluster class: adding hops increases the residual. -/
def isCluster (gamma : ℝ) : Prop :=
  0 < gamma

end TINProofs.C5

end
