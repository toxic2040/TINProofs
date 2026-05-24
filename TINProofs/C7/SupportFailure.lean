/-
  C7: Support Failure via Rate-Distortion (Theorem 2).

  Three results:
  1. support_necessary: reconstruction exists -> R(eps) <= C_b
  2. support_failure: R(eps) > C_b -> any reconstruction has eps_eff > eps
  3. below_threshold_unsupportable: eps < eps* -> any reconstruction has eps_eff > eps
-/
import TINProofs.C7.Defs

noncomputable section

namespace TINProofs.C7

/--
Necessary condition for supportability.

Any reconstruction satisfying the DPI+capacity chain has R(eps_eff) <= C_b.
Proof: R(eps_eff) <= I <= C_b by transitivity.
-/
theorem support_necessary (S : SupportSetup)
    (w : ReconstructionWitness S) :
    S.R w.eps_eff ≤ S.C_b :=
  le_trans w.h_rd_lower w.h_capacity

/--
Support failure (Theorem 2, contrapositive form).

If R(eps) > C_b, then any reconstruction w has eps < w.eps_eff.
No reconstruction can achieve resolution eps or finer.

Proof by contradiction: if w.eps_eff <= eps, then by antitone R,
R(eps) <= R(w.eps_eff) <= I <= C_b, contradicting R(eps) > C_b.
-/
theorem support_failure (S : SupportSetup) (ε : ℝ)
    (h_exceed : S.C_b < S.R ε) :
    ∀ (w : ReconstructionWitness S), ε < w.eps_eff := by
  intro w
  by_contra h
  push Not at h
  have hR : S.R ε ≤ S.R w.eps_eff := S.hR_antitone h
  have h_le : S.R ε ≤ S.C_b :=
    le_trans hR (le_trans w.h_rd_lower w.h_capacity)
  have h_bad : S.C_b < S.C_b := lt_of_lt_of_le h_exceed h_le
  exact (lt_irrefl S.C_b) h_bad

/--
Below-threshold unsupportability.

If eps < eps*, no reconstruction achieves resolution eps.
Combines the threshold characterization with support_failure.
-/
theorem below_threshold_unsupportable (S : SupportSetup)
    (T : SupportThreshold S) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_below : ε < T.eps_star) :
    ∀ (w : ReconstructionWitness S), ε < w.eps_eff := by
  exact support_failure S ε (T.h_below ε hε_pos hε_below)

/--
Any reconstruction's achieved resolution is at least eps_star.

This is the form C8 (Boundary Re-description) needs: for any
reconstruction w, eps_star <= w.eps_eff.
-/
theorem eps_star_le_eps_eff (S : SupportSetup)
    (T : SupportThreshold S)
    (w : ReconstructionWitness S) :
    T.eps_star ≤ w.eps_eff := by
  by_contra h
  push Not at h
  have h_bad : w.eps_eff < w.eps_eff :=
    below_threshold_unsupportable S T w.eps_eff w.heps_eff_pos h w
  exact (lt_irrefl w.eps_eff) h_bad

end TINProofs.C7

end
