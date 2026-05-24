/-
  C8: Boundary Re-description Theorem -- definitions

  Extends C7's support setup with the optimal boundary summary Z*
  and the three consequences of support failure forcing description
  through the boundary at the threshold resolution.
-/
import TINProofs.C7.SupportFailure

noncomputable section

namespace TINProofs.C8

open TINProofs.C7

/--
The optimal boundary summary Z* that saturates the channel.

Given a SupportSetup and SupportThreshold from C7, Z* is
characterized by:
  - It achieves exactly eps_star (threshold resolution)
  - It saturates the channel: I(Y; Z*) = C_b
  - R(eps_star) = C_b (rate-distortion at threshold equals capacity)

These are trust boundaries from rate-distortion achievability
(Shannon's source coding theorem, forward direction).
-/
structure BoundarySummary (S : SupportSetup) (T : SupportThreshold S) where
  I_star : ℝ
  h_saturates : I_star = S.C_b
  h_rd_at_threshold : S.R T.eps_star = S.C_b

/--
A general exterior reconstruction: any observer trying to describe
the interior from outside. Carries the same DPI+capacity chain as
C7's ReconstructionWitness, but with additional structure for the
re-description consequences.

  eps_eff: achieved distortion
  I_recon: mutual information used
  h_channel: I_recon <= C_b (DPI + capacity, from C7)
  h_rd: R(eps_eff) <= I_recon (rate-distortion lower bound)
-/
structure ExteriorReconstruction (S : SupportSetup) where
  eps_eff : ℝ
  I_recon : ℝ
  heps_eff_pos : 0 < eps_eff
  hI_nonneg : 0 ≤ I_recon
  h_rd : S.R eps_eff ≤ I_recon
  h_channel : I_recon ≤ S.C_b

/-- Convert an ExteriorReconstruction to a C7 ReconstructionWitness. -/
def ExteriorReconstruction.toWitness {S : SupportSetup}
    (r : ExteriorReconstruction S) : ReconstructionWitness S where
  I := r.I_recon
  eps_eff := r.eps_eff
  heps_eff_pos := r.heps_eff_pos
  hI_nonneg := r.hI_nonneg
  h_rd_lower := r.h_rd
  h_capacity := r.h_channel

end TINProofs.C8

end
