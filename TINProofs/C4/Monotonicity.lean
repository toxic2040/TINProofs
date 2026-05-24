/-
  C4 Lemma 2.6: temporal reachability is monotone under augmentation.
-/
import TINProofs.C4.Factorization

open MeasureTheory Set

noncomputable section

namespace TINProofs.C4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `S_T` is monotone under augmentation. -/
theorem st_monotone (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt') :
    tt.ST ≤ tt'.ST := by
  unfold TemporalTransport.ST
  rw [h_same_measure]
  exact measure_mono aug.h_F_mono

/-- Real-valued `S_T` is monotone under augmentation. -/
theorem stReal_monotone (tt tt' : TemporalTransport Ω)
    (h_same_measure : tt.μ = tt'.μ)
    (aug : Augmentation tt tt') :
    tt.STReal ≤ tt'.STReal := by
  have hmono : tt.ST ≤ tt'.ST := st_monotone tt tt' h_same_measure aug
  have hfinite : tt'.ST ≠ ⊤ := by
    simp [TemporalTransport.ST, measure_ne_top tt'.μ tt'.F]
  simp [TemporalTransport.STReal, ENNReal.toReal_mono hfinite hmono]

end TINProofs.C4

end
