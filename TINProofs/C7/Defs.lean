/-
  C7: Support Failure via Rate-Distortion -- definitions

  Scalar data encoding the information-theoretic setup for the
  support failure theorem (Theorem 2, discussion v0.9 Section 15).
  The DPI, capacity bound, and rate-distortion lower bound are
  encoded as hypotheses in witness structures.
-/
import Mathlib

noncomputable section

namespace TINProofs.C7

/-- Scalar data for the support failure theorem.

  C_b is the boundary channel capacity (kappa * C(dU)).
  R is the rate-distortion function R_U(eps).
-/
structure SupportSetup where
  C_b : ℝ
  R : ℝ → ℝ
  hC_b_pos : 0 < C_b
  hR_antitone : Antitone R
  hR_nonneg : ∀ ε, 0 ≤ R ε

/--
A reconstruction witness: an observer achieves distortion eps_eff
with mutual information I, subject to the DPI+capacity chain.

h_rd_lower encodes the rate-distortion lower bound: R(eps_eff) <= I.
h_capacity encodes DPI + A4: I(Y;Y_hat) <= I(Y;Z) <= C_b.
-/
structure ReconstructionWitness (S : SupportSetup) where
  I : ℝ
  eps_eff : ℝ
  heps_eff_pos : 0 < eps_eff
  hI_nonneg : 0 ≤ I
  h_rd_lower : S.R eps_eff ≤ I
  h_capacity : I ≤ S.C_b

/--
A support threshold: eps_star separates supportable (above) from
unsupportable (below) resolutions.

  Above eps_star: R(eps) <= C_b (supportable in principle).
  Below eps_star: R(eps) > C_b (unsupportable by Theorem 2).
-/
structure SupportThreshold (S : SupportSetup) where
  eps_star : ℝ
  heps_star_pos : 0 < eps_star
  h_above : ∀ ε, eps_star < ε → S.R ε ≤ S.C_b
  h_below : ∀ ε, 0 < ε → ε < eps_star → S.C_b < S.R ε

end TINProofs.C7

end
