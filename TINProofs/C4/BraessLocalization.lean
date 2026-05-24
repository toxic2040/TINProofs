/-
  C4 Remark 2.8: any Braess-style delivery-ratio decrease under augmentation
  is localized in the efficiency factor.
-/
import TINProofs.C4.Monotonicity

open MeasureTheory Set

noncomputable section

namespace TINProofs.C4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- If delivery ratio decreases under augmentation, efficiency decreases. -/
theorem braess_in_eta (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt')
    (hF : 0 < (tt.μ tt.F).toReal)
    (_hF' : 0 < (tt'.μ tt'.F).toReal)
    (h_dr_decrease : (tt'.μ tt'.D).toReal < (tt.μ tt.D).toReal) :
    (tt'.μ tt'.D).toReal / (tt'.μ tt'.F).toReal <
      (tt.μ tt.D).toReal / (tt.μ tt.F).toReal := by
  have hST_mono : (tt.μ tt.F).toReal ≤ (tt'.μ tt'.F).toReal := by
    simpa [TemporalTransport.STReal, TemporalTransport.ST] using
      stReal_monotone tt tt' h_same_measure aug
  have hDR_nonneg : 0 ≤ (tt.μ tt.D).toReal := ENNReal.toReal_nonneg
  exact div_lt_div₀ h_dr_decrease hST_mono hDR_nonneg hF

/-- Same localization statement in the named real-valued factors. -/
theorem braess_in_etaReal (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt')
    (hF : 0 < tt.STReal)
    (_hF' : 0 < tt'.STReal)
    (h_dr_decrease : tt'.DRReal < tt.DRReal) :
    tt'.etaReal < tt.etaReal := by
  unfold TemporalTransport.etaReal
  exact div_lt_div₀ h_dr_decrease
    (stReal_monotone tt tt' h_same_measure aug)
    ENNReal.toReal_nonneg hF

end TINProofs.C4

end
