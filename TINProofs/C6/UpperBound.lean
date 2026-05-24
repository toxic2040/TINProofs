/-
  C6 Lemma 2: packing-covering duality implies upper bound on covering number.

  A maximal packing of M disjoint half-radius balls in U implies
  M <= (2^gamma / C1) * |U| * epsilon^{-gamma}.
  By maximality, the doubled balls cover U, so N_U(epsilon) <= M.
-/
import TINProofs.C6.Defs

noncomputable section

namespace TINProofs.C6

/--
A maximal packing of U by M disjoint balls of radius epsilon/2.
Each packing ball captures at least C1 * (epsilon/2)^gamma points from U
(Ahlfors lower regularity). Disjointness + lower regularity gives
M * C1 * (epsilon/2)^gamma <= |U|. Maximality implies the doubled
balls cover U, so M is an upper bound on N_U(epsilon).
-/
structure PackingWitness (S : AhlforsSetup) where
  M : ℕ
  epsilon : ℝ
  heps_pos : 0 < epsilon
  hM_pos : 0 < M
  h_packing : (M : ℝ) * S.C1 * (epsilon / 2) ^ S.gamma ≤ (S.cardU : ℝ)

/--
Rewrite (epsilon/2)^gamma as epsilon^gamma / 2^gamma.
-/
theorem half_rpow_eq (epsilon gamma : ℝ) (heps : 0 < epsilon) (_hgamma : 0 < gamma) :
    (epsilon / 2) ^ gamma = epsilon ^ gamma / (2 : ℝ) ^ gamma := by
  exact Real.div_rpow (le_of_lt heps) (by norm_num) gamma

/--
Upper bound on covering number from packing-covering duality.

From M * C1 * eps^gamma / 2^gamma <= |U|, rearranging:
  M <= |U| * 2^gamma / (C1 * eps^gamma) = (2^gamma/C1) * |U| * eps^{-gamma}.
-/
theorem covering_upper_bound (S : AhlforsSetup) (pk : PackingWitness S) :
    (pk.M : ℝ) ≤ upperConst S * (S.cardU : ℝ) * pk.epsilon ^ (-S.gamma) := by
  have hhalf_pos : 0 < pk.epsilon / 2 := div_pos pk.heps_pos (by norm_num)
  have hhalfpow_pos : 0 < (pk.epsilon / 2) ^ S.gamma :=
    Real.rpow_pos_of_pos hhalf_pos S.gamma
  have hden_pos : 0 < S.C1 * (pk.epsilon / 2) ^ S.gamma :=
    mul_pos S.hC1_pos hhalfpow_pos
  have hdiv : (pk.M : ℝ) ≤ (S.cardU : ℝ) / (S.C1 * (pk.epsilon / 2) ^ S.gamma) := by
    refine (le_div_iff₀ hden_pos).mpr ?_
    calc
      (pk.M : ℝ) * (S.C1 * (pk.epsilon / 2) ^ S.gamma)
          = (pk.M : ℝ) * S.C1 * (pk.epsilon / 2) ^ S.gamma := by ring
      _ ≤ (S.cardU : ℝ) := pk.h_packing
  have hepspow_pos : 0 < pk.epsilon ^ S.gamma :=
    Real.rpow_pos_of_pos pk.heps_pos S.gamma
  have htwopow_pos : 0 < (2 : ℝ) ^ S.gamma :=
    Real.rpow_pos_of_pos (by norm_num) S.gamma
  calc
    (pk.M : ℝ) ≤ (S.cardU : ℝ) / (S.C1 * (pk.epsilon / 2) ^ S.gamma) := hdiv
    _ = upperConst S * (S.cardU : ℝ) * pk.epsilon ^ (-S.gamma) := by
      unfold upperConst
      rw [half_rpow_eq pk.epsilon S.gamma pk.heps_pos S.hgamma_pos]
      rw [Real.rpow_neg (le_of_lt pk.heps_pos) S.gamma]
      field_simp [ne_of_gt S.hC1_pos, ne_of_gt hepspow_pos, ne_of_gt htwopow_pos]

end TINProofs.C6

end
