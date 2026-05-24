/-
  C4 Lemma 2.1 consequences: delivery implies feasibility.
-/
import TINProofs.C4.Defs

open MeasureTheory Set

noncomputable section

namespace TINProofs.C4

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A delivered but infeasible sample cannot occur. -/
theorem delivery_inter_infeasible_eq_empty (tt : TemporalTransport Ω) :
    tt.D ∩ tt.Fᶜ = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hx.2 (tt.h_incl hx.1))
  · intro hx
    exact False.elim hx

/-- `D ⊆ F` implies `P(D ∩ Fᶜ) = 0`. -/
theorem delivery_zero_when_infeasible (tt : TemporalTransport Ω) :
    tt.μ (tt.D ∩ tt.Fᶜ) = 0 := by
  rw [delivery_inter_infeasible_eq_empty tt]
  exact measure_empty

/-- Delivery probability is bounded by feasibility probability. -/
theorem delivery_measure_le_feasible (tt : TemporalTransport Ω) :
    tt.μ tt.D ≤ tt.μ tt.F :=
  measure_mono tt.h_incl

end TINProofs.C4

end
