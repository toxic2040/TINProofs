import Mathlib

open Real Set

noncomputable section

namespace TINProofs.C1

/-- A path in the exposure-reliability plane. -/
structure PathData where
  T : ℝ
  Q : ℝ
  hT_nonneg : 0 ≤ T
  hQ_pos : 0 < Q
  hQ_le : Q ≤ 1
  deriving DecidableEq

/-- Path action at commodity hazard rate `lam`. -/
def PathData.action (p : PathData) (lam : ℝ) : ℝ :=
  -Real.log p.Q + lam * p.T

/-- Path value at commodity hazard rate `lam`. -/
def PathData.value (p : PathData) (lam : ℝ) : ℝ :=
  Real.log p.Q - lam * p.T

/-- Alias for path action at commodity hazard rate `lam`. -/
def pathAction (p : PathData) (lam : ℝ) : ℝ :=
  p.action lam

/-- Alias for path value at commodity hazard rate `lam`. -/
def pathValue (p : PathData) (lam : ℝ) : ℝ :=
  p.value lam

/-- A nonempty finite set of feasible paths. -/
structure CommodityHull where
  paths : Finset PathData
  hnonempty : paths.Nonempty

/-- Support function: the minimum path action at `lam`. -/
def CommodityHull.support (ch : CommodityHull) (lam : ℝ) : ℝ :=
  ch.paths.inf' ch.hnonempty (fun p => p.action lam)

/-- Value function: the maximum path value at `lam`. -/
def CommodityHull.valueFn (ch : CommodityHull) (lam : ℝ) : ℝ :=
  ch.paths.sup' ch.hnonempty (fun p => p.value lam)

/-- Crossover slope between two paths with distinct exposure times. -/
def crossoverSlope (pi pj : PathData) (_hT : pi.T ≠ pj.T) : ℝ :=
  (Real.log pj.Q - Real.log pi.Q) / (pj.T - pi.T)

end TINProofs.C1

end
