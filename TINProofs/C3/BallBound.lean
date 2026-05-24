/-
  C3 Lemma 5: derivative bound inside the critical ball.
-/
import TINProofs.C3.VDotDecomp
import TINProofs.C3.QuadBound
import TINProofs.C3.RemainderBound

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/-- Combining the decomposition, quadratic lower bound, and remainder bound. -/
theorem vdot_le_quadratic_plus_cubic :
    P.Vdot ≤ -S.q * P.rho ^ 2 + S.opNormA * S.M * P.rho ^ 3 := by
  calc
    P.Vdot = -P.quad + P.remainder := vdot_decomposition P
    _ ≤ -(S.q * P.rho ^ 2) + S.opNormA * S.M * P.rho ^ 3 := by
      exact add_le_add (negative_quadratic_term_upper P) (remainder_upper_bound P)
    _ = -S.q * P.rho ^ 2 + S.opNormA * S.M * P.rho ^ 3 := by
      ring

/-- On `rho < r*`, the nonlinear term consumes at most half the quadratic margin. -/
theorem vdot_bound_on_ball (hball : P.rho < criticalRadius S) :
    P.Vdot ≤ -(S.q / 2) * P.rho ^ 2 := by
  have hsmall : P.rho < S.q / (2 * S.opNormA * S.M) :=
    lt_of_lt_of_le hball (min_le_right S.r0 (S.q / (2 * S.opNormA * S.M)))
  have hden_pos : 0 < 2 * S.opNormA * S.M := by
    nlinarith [S.hOpNormA_pos, S.hM_pos]
  have hprod_lt : P.rho * (2 * S.opNormA * S.M) < S.q :=
    (lt_div_iff₀ hden_pos).mp hsmall
  have hcoeff_lt : S.opNormA * S.M * P.rho < S.q / 2 := by
    nlinarith
  have hsq_nonneg : 0 ≤ P.rho ^ 2 := sq_nonneg P.rho
  have hcubic :
      S.opNormA * S.M * P.rho ^ 3 ≤ (S.q / 2) * P.rho ^ 2 := by
    calc
      S.opNormA * S.M * P.rho ^ 3 =
          (S.opNormA * S.M * P.rho) * P.rho ^ 2 := by
        ring
      _ ≤ (S.q / 2) * P.rho ^ 2 := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hcoeff_lt) hsq_nonneg
  calc
    P.Vdot ≤ -S.q * P.rho ^ 2 + S.opNormA * S.M * P.rho ^ 3 :=
      vdot_le_quadratic_plus_cubic P
    _ ≤ -S.q * P.rho ^ 2 + (S.q / 2) * P.rho ^ 2 := by
      nlinarith [hcubic]
    _ = -(S.q / 2) * P.rho ^ 2 := by
      ring

end TINProofs.C3

end
