/-
  C9: S_T-eta Coupling Bound via Pinsker -- definitions

  Source: discussion v0.9 Section 21.3

  The covariance between S_T and eta under coarse information G
  is bounded by sqrt(2 * I(S; eta | G)), where both factors
  lie in [0,1]. This is a Pinsker-type inequality for bounded
  random variables.
-/
import Mathlib

noncomputable section

namespace TINProofs.C9

/-- Scalar data for the coupling bound theorem.

  S and eta are [0,1]-valued random variables (infrastructure
  reachability and routing efficiency). Their covariance under
  coarse information G is bounded by the conditional mutual
  information between them.
-/
structure CouplingSetup where
  S_val : ℝ
  eta_val : ℝ
  covSEta : ℝ
  mi : ℝ
  varS : ℝ
  varEta : ℝ
  hS_nonneg : 0 ≤ S_val
  hS_le_one : S_val ≤ 1
  hEta_nonneg : 0 ≤ eta_val
  hEta_le_one : eta_val ≤ 1
  hmi_nonneg : 0 ≤ mi
  hvarS_nonneg : 0 ≤ varS
  hvarEta_nonneg : 0 ≤ varEta

end TINProofs.C9

end
