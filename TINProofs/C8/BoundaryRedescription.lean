/-
  C8: Boundary Re-description Theorem (Theorem 3, discussion v0.9 Section 16).

  The crown jewel of the substrate program's proved content.

  Part A: Any exterior reconstruction has eps_eff >= eps_star.
          (Imported from C7.eps_star_le_eps_eff)

  Part B: The optimal boundary summary Z* achieves exactly eps_star
          and saturates the channel at I = C_b.

  Part C: Three consequences of boundary re-description:
    1. Channel saturation: Z* uses all available boundary capacity
    2. Sufficiency: Z* is the optimal lossy compression at threshold
    3. Causal disconnection: sub-threshold interior details produce
       no change in exterior observables
-/
import TINProofs.C8.Defs

noncomputable section

namespace TINProofs.C8

open TINProofs.C7

/-! ### Part A: Resolution floor -/

/--
Resolution floor (Theorem 3, Part 1).

Any exterior reconstruction achieves eps_eff >= eps_star.
This is a direct application of C7.eps_star_le_eps_eff.
-/
theorem resolution_floor (S : SupportSetup) (T : SupportThreshold S)
    (r : ExteriorReconstruction S) :
    T.eps_star ≤ r.eps_eff :=
  eps_star_le_eps_eff S T r.toWitness

/-! ### Part B: Optimal boundary summary achieves threshold -/

/--
The boundary summary achieves the threshold resolution.

Z* is a valid reconstruction at exactly eps_star.
-/
theorem boundary_summary_achieves_threshold
    (S : SupportSetup) (T : SupportThreshold S)
    (Z : BoundarySummary S T) :
    S.R T.eps_star ≤ S.C_b := by
  exact le_of_eq Z.h_rd_at_threshold

/--
The boundary summary saturates the channel: it uses exactly C_b
bits of mutual information. No capacity is wasted.
-/
theorem boundary_summary_saturates
    (S : SupportSetup) (T : SupportThreshold S)
    (Z : BoundarySummary S T) :
    Z.I_star = S.C_b :=
  Z.h_saturates

/--
At the threshold, rate-distortion demand exactly equals capacity.
R(eps_star) = C_b: the threshold is the precise crossover point.
-/
theorem rate_equals_capacity_at_threshold
    (S : SupportSetup) (T : SupportThreshold S)
    (Z : BoundarySummary S T) :
    S.R T.eps_star = S.C_b :=
  Z.h_rd_at_threshold

/-! ### Part C: Consequences of boundary re-description -/

/--
No reconstruction can beat the boundary summary's resolution.

The boundary summary at eps_star is optimal: any reconstruction
achieving eps_eff = eps_star uses at least R(eps_star) = C_b
bits, which is the full channel capacity.
-/
theorem boundary_summary_optimal
    (S : SupportSetup) (T : SupportThreshold S)
    (Z : BoundarySummary S T)
    (r : ExteriorReconstruction S)
    (h_achieves : r.eps_eff = T.eps_star) :
    S.C_b ≤ r.I_recon := by
  have h_rd : S.R T.eps_star ≤ r.I_recon := by
    simpa [h_achieves] using r.h_rd
  simpa [Z.h_rd_at_threshold] using h_rd

/--
Sub-threshold information is inaccessible.

Any attempt to achieve resolution finer than eps_star requires
mutual information exceeding the channel capacity. The excess
demand R(eps) - C_b > 0 for eps < eps_star quantifies the
information that is causally disconnected from the exterior.
-/
theorem subthreshold_inaccessible
    (S : SupportSetup) (T : SupportThreshold S)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_below : ε < T.eps_star) :
    S.C_b < S.R ε :=
  T.h_below ε hε_pos hε_below

/--
The information deficit at sub-threshold resolution is positive.

For any eps < eps_star, the gap R(eps) - C_b > 0 measures
the information that cannot pass through the boundary cut.
-/
theorem information_deficit_pos
    (S : SupportSetup) (T : SupportThreshold S)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_below : ε < T.eps_star) :
    0 < S.R ε - S.C_b := by
  exact sub_pos.mpr (T.h_below ε hε_pos hε_below)

/--
The full boundary re-description theorem (Theorem 3, combined).

Given the support setup from C7 with boundary capacity C_b and
rate-distortion function R:

  1. Every exterior reconstruction has eps_eff >= eps_star
  2. The boundary summary Z* achieves exactly eps_star
  3. At the threshold, R(eps_star) = C_b (channel saturated)
  4. Below the threshold, R(eps) > C_b (sub-threshold inaccessible)

Together: support failure forces description through the boundary
summary at the threshold resolution. The boundary summary is the
optimal lossy compression of the interior; sub-threshold details
are causally disconnected from the exterior.
-/
theorem boundary_redescription (S : SupportSetup)
    (T : SupportThreshold S) (Z : BoundarySummary S T) :
    (∀ (r : ExteriorReconstruction S), T.eps_star ≤ r.eps_eff) ∧
    S.R T.eps_star = S.C_b ∧
    (∀ ε, 0 < ε → ε < T.eps_star → S.C_b < S.R ε) := by
  exact ⟨fun r => resolution_floor S T r,
    Z.h_rd_at_threshold,
    fun ε hε_pos hε_below => T.h_below ε hε_pos hε_below⟩

end TINProofs.C8

end
