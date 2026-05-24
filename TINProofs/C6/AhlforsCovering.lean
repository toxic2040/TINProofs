/-
  C6: Ahlfors Covering and Volume Scaling — main theorem.

  Theorem 1 from discussion v0.9 Section 13.
  Under Ahlfors gamma-regularity on a finite region U,
  the covering number N_U(epsilon) satisfies:

    (1/C2) |U| eps^{-gamma} <= N_U(eps) <= (2^gamma/C1) |U| eps^{-gamma}

  Corollary: the graph-scaling ansatz D_U(eps) ~ K_U * eps^{-gamma} holds
  with K_U in [b * A1 * |U|, b * A2 * |U|].
-/
import TINProofs.C6.LowerBound
import TINProofs.C6.UpperBound

noncomputable section

namespace TINProofs.C6

/--
Ahlfors Covering Theorem (Theorem 1).

Under Ahlfors gamma-regularity, the covering number N satisfies
two-sided bounds with constants A1 = 1/C2 and A2 = 2^gamma/C1.
-/
theorem ahlfors_covering (S : AhlforsSetup)
    (cov : CoveringWitness S) (pk : PackingWitness S)
    (h_same_eps : cov.epsilon = pk.epsilon)
    (h_N_le_M : (cov.N : ℝ) ≤ (pk.M : ℝ)) :
    lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) ≤ (cov.N : ℝ) ∧
    (cov.N : ℝ) ≤ upperConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) := by
  constructor
  · exact covering_lower_bound S cov
  · calc
      (cov.N : ℝ) ≤ (pk.M : ℝ) := h_N_le_M
      _ ≤ upperConst S * (S.cardU : ℝ) * pk.epsilon ^ (-S.gamma) :=
        covering_upper_bound S pk
      _ = upperConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) := by
        rw [h_same_eps]

/--
Corollary 1.1: Ansatz validity.

If D_U(epsilon) = b * N_U(epsilon) with b > 0, then
D_U is bounded between b * A1 * |U| * eps^{-gamma} and
b * A2 * |U| * eps^{-gamma}.
-/
theorem ansatz_validity (S : AhlforsSetup)
    (cov : CoveringWitness S) (pk : PackingWitness S)
    (h_same_eps : cov.epsilon = pk.epsilon)
    (h_N_le_M : (cov.N : ℝ) ≤ (pk.M : ℝ))
    (b : ℝ) (hb : 0 < b) :
    b * lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) ≤ b * (cov.N : ℝ) ∧
    b * (cov.N : ℝ) ≤ b * upperConst S * (S.cardU : ℝ) * cov.epsilon ^ (-S.gamma) := by
  obtain ⟨hlower, hupper⟩ := ahlfors_covering S cov pk h_same_eps h_N_le_M
  constructor
  · have h := mul_le_mul_of_nonneg_left hlower (le_of_lt hb)
    simpa [mul_assoc] using h
  · have h := mul_le_mul_of_nonneg_left hupper (le_of_lt hb)
    simpa [mul_assoc] using h

end TINProofs.C6

end
