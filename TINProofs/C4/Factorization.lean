/-
  C4 Proposition 2.2: delivery ratio factors through temporal reachability
  and conditional efficiency.
-/
import TINProofs.C4.Inclusion

open MeasureTheory Set

noncomputable section

namespace TINProofs.C4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Exact `ENNReal` factorization: `DR = S_T * eta`. -/
theorem exact_factorization (tt : TemporalTransport Ω) (hF : tt.ST ≠ 0) :
    tt.DR = tt.ST * tt.eta := by
  have hF_ne_zero : tt.μ tt.F ≠ 0 := by
    simpa [TemporalTransport.ST] using hF
  unfold TemporalTransport.DR TemporalTransport.ST TemporalTransport.eta
  rw [ENNReal.mul_div_cancel hF_ne_zero (measure_ne_top tt.μ tt.F)]

/-- Real-valued version of the same factorization. -/
theorem exact_factorization_real (tt : TemporalTransport Ω) (hF : tt.STReal ≠ 0) :
    tt.DRReal = tt.STReal * tt.etaReal := by
  rw [TemporalTransport.etaReal]
  exact (mul_div_cancel₀ tt.DRReal hF).symm

end TINProofs.C4

end
