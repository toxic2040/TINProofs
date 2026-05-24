/-
  C5: elementary properties of the sparse-law factors.
-/
import TINProofs.C5.Defs

open MeasureTheory Real

noncomputable section

namespace TINProofs.C5

/-- Chain attenuation is positive. -/
theorem etaLyap_pos (s : SparseLawSetup) : 0 < s.etaLyap := by
  unfold SparseLawSetup.etaLyap
  exact Real.exp_pos _

/-- Chain attenuation is less than one when `E_H > 0` and `lyap < 0`. -/
theorem etaLyap_lt_one (s : SparseLawSetup) : s.etaLyap < 1 := by
  unfold SparseLawSetup.etaLyap
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by nlinarith [s.hEH_pos, s.hlyap_neg])

/-- `Phi` is positive when `eta` is positive. -/
theorem phi_pos (s : SparseLawSetup) (heta : 0 < s.eta) : 0 < s.Phi := by
  unfold SparseLawSetup.Phi
  exact div_pos heta (etaLyap_pos s)

/-- The mean of `log p_h` is negative when every hop probability lies in `(0, 1)`. -/
theorem lyapunov_exponent_neg {n : ℕ} (ps : Fin n → ℝ)
    (hps_pos : ∀ i, 0 < ps i) (hps_lt : ∀ i, ps i < 1)
    (hn : 0 < n) :
    (∑ i, Real.log (ps i)) / (n : ℝ) < 0 := by
  have hsum_neg : (∑ i : Fin n, Real.log (ps i)) < 0 := by
    have hnonempty : (Finset.univ : Finset (Fin n)).Nonempty :=
      ⟨⟨0, hn⟩, by simp⟩
    exact Finset.sum_neg
      (fun i _ => Real.log_neg (hps_pos i) (hps_lt i))
      hnonempty
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  exact div_neg_of_neg_of_pos hsum_neg hn_pos

end TINProofs.C5

end
