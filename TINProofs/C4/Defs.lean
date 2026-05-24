/-
  C4: Temporal transport factorization -- definitions.

  The C4 layer works at the level of abstract probability events rather than
  concrete temporal graphs.
-/
import Mathlib

open MeasureTheory Set

noncomputable section

namespace TINProofs.C4

/--
A temporal transport instance: a probability space with delivery and
feasibility events.
-/
structure TemporalTransport (Ω : Type*) [MeasurableSpace Ω] where
  μ : Measure Ω
  hprob : IsProbabilityMeasure μ
  D : Set Ω
  F : Set Ω
  hD : MeasurableSet D
  hF : MeasurableSet F
  h_incl : D ⊆ F

namespace TemporalTransport

instance instIsProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω]
    (tt : TemporalTransport Ω) : IsProbabilityMeasure tt.μ :=
  tt.hprob

/-- Delivery ratio: `P(D)`. -/
def DR {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ENNReal :=
  tt.μ tt.D

/-- Temporal reachability: `P(F)`. -/
def ST {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ENNReal :=
  tt.μ tt.F

/-- Transport efficiency: `P(D | F)`, represented as `P(D) / P(F)`. -/
def eta {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ENNReal :=
  tt.μ tt.D / tt.μ tt.F

/-- Real-valued delivery ratio, useful for ratio comparisons. -/
def DRReal {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ℝ :=
  (tt.DR).toReal

/-- Real-valued temporal reachability, useful for ratio comparisons. -/
def STReal {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ℝ :=
  (tt.ST).toReal

/-- Real-valued efficiency. -/
def etaReal {Ω : Type*} [MeasurableSpace Ω] (tt : TemporalTransport Ω) : ℝ :=
  tt.DRReal / tt.STReal

end TemporalTransport

/--
An augmentation keeps the same event space and preserves all previously
feasible samples.
-/
structure Augmentation {Ω : Type*} [MeasurableSpace Ω]
    (tt tt' : TemporalTransport Ω) where
  h_F_mono : tt.F ⊆ tt'.F

end TINProofs.C4

end
