/-
  C3 main theorem: Lyapunov radius of validity.
-/
import TINProofs.C3.EigenSandwich
import TINProofs.C3.BallBound

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/-- The critical radius is positive under the setup hypotheses. -/
theorem criticalRadius_pos (S : LyapunovSetup) :
    0 < criticalRadius S := by
  have hden_pos : 0 < 2 * S.opNormA * S.M := by
    nlinarith [S.hOpNormA_pos, S.hM_pos]
  have hfrac_pos : 0 < S.q / (2 * S.opNormA * S.M) :=
    div_pos S.hq_pos hden_pos
  exact lt_min S.hr0_pos hfrac_pos

/--
Inside the critical ball, the Lyapunov derivative has the exponential
decay rate `q / (2 * alphaMax)`.
-/
theorem lyapunov_radius_of_validity (hball : P.rho < criticalRadius S) :
    P.Vdot ≤ -(lyapunovDecayRate S) * P.V := by
  have hball_bound : P.Vdot ≤ -(S.q / 2) * P.rho ^ 2 :=
    vdot_bound_on_ball P hball
  have hupper : P.V ≤ S.alphaMax * P.rho ^ 2 :=
    eigen_sandwich_upper P
  have hden_pos : 0 < 2 * S.alphaMax := by
    nlinarith [S.hAlphaMax_pos]
  have hrate_pos : 0 < S.q / (2 * S.alphaMax) :=
    div_pos S.hq_pos hden_pos
  have hcoef_nonpos : -(S.q / (2 * S.alphaMax)) ≤ 0 := by
    nlinarith
  have hscaled :
      -(S.q / (2 * S.alphaMax)) * (S.alphaMax * P.rho ^ 2) ≤
        -(S.q / (2 * S.alphaMax)) * P.V :=
    mul_le_mul_of_nonpos_left hupper hcoef_nonpos
  have hrewrite :
      -(S.q / 2) * P.rho ^ 2 =
        -(S.q / (2 * S.alphaMax)) * (S.alphaMax * P.rho ^ 2) := by
    field_simp [ne_of_gt S.hAlphaMax_pos]
  calc
    P.Vdot ≤ -(S.q / 2) * P.rho ^ 2 := hball_bound
    _ = -(S.q / (2 * S.alphaMax)) * (S.alphaMax * P.rho ^ 2) := hrewrite
    _ ≤ -(S.q / (2 * S.alphaMax)) * P.V := hscaled
    _ = -(lyapunovDecayRate S) * P.V := by
      rfl

/--
Any Lyapunov sublevel value below `alphaMin * r*^2` lies inside the
critical ball.
-/
theorem sublevel_inside_critical_ball {V0 : ℝ}
    (hV : P.V ≤ V0)
    (hV0 : V0 < S.alphaMin * criticalRadius S ^ 2) :
    P.rho < criticalRadius S := by
  have hchain :
      S.alphaMin * P.rho ^ 2 < S.alphaMin * criticalRadius S ^ 2 :=
    lt_of_le_of_lt (le_trans (eigen_sandwich_lower P) hV) hV0
  have hsquares : P.rho ^ 2 < criticalRadius S ^ 2 :=
    by nlinarith [S.hAlphaMin_pos, hchain]
  have hradius_pos : 0 < criticalRadius S := criticalRadius_pos S
  nlinarith [P.hrho_nonneg, hradius_pos, hsquares,
    sq_nonneg (P.rho - criticalRadius S)]

/--
Algebraic forward-invariance criterion: on a boundary value below
`alphaMin * r*^2`, the Lyapunov derivative is nonpositive.
-/
theorem sublevel_boundary_vdot_nonpos {V0 : ℝ}
    (hV : P.V = V0)
    (hV0 : V0 < S.alphaMin * criticalRadius S ^ 2) :
    P.Vdot ≤ 0 := by
  have hinside : P.rho < criticalRadius S :=
    sublevel_inside_critical_ball P (le_of_eq hV) hV0
  have hdecay : P.Vdot ≤ -(lyapunovDecayRate S) * P.V :=
    lyapunov_radius_of_validity P hinside
  have hV_nonneg : 0 ≤ P.V := by
    have hlow : S.alphaMin * P.rho ^ 2 ≤ P.V := eigen_sandwich_lower P
    have hrho_sq_nonneg : 0 ≤ P.rho ^ 2 := sq_nonneg P.rho
    nlinarith [S.hAlphaMin_pos, hlow, hrho_sq_nonneg]
  have hrate_pos : 0 < lyapunovDecayRate S := by
    unfold lyapunovDecayRate
    have hden_pos : 0 < 2 * S.alphaMax := by
      nlinarith [S.hAlphaMax_pos]
    exact div_pos S.hq_pos hden_pos
  have hright_nonpos : -(lyapunovDecayRate S) * P.V ≤ 0 := by
    nlinarith
  exact le_trans hdecay hright_nonpos

end TINProofs.C3

end
