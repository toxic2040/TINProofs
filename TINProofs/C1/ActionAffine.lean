import TINProofs.C1.Defs

open Real Set

noncomputable section

namespace TINProofs.C1

/-- Path action is affine in the commodity hazard rate. -/
theorem action_affine (p : PathData) (lam1 lam2 : ℝ) (a b : ℝ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = 1) :
    p.action (a * lam1 + b * lam2) = a * p.action lam1 + b * p.action lam2 := by
  unfold PathData.action
  have hconst : -Real.log p.Q = a * (-Real.log p.Q) + b * (-Real.log p.Q) := by
    calc
      -Real.log p.Q = (a + b) * (-Real.log p.Q) := by rw [hab]; ring
      _ = a * (-Real.log p.Q) + b * (-Real.log p.Q) := by ring
  conv_lhs => rw [hconst]
  ring

/-- Path action is convex on all hazard rates. -/
theorem action_convexOn (p : PathData) : ConvexOn ℝ univ p.action := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simpa [smul_eq_mul] using le_of_eq (action_affine p x y a b ha hb hab)

/-- Path action is concave on all hazard rates. -/
theorem action_concaveOn (p : PathData) : ConcaveOn ℝ univ p.action := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simpa [smul_eq_mul] using le_of_eq (action_affine p x y a b ha hb hab).symm

/-- Per-path value is affine in the commodity hazard rate. -/
theorem value_affine (p : PathData) (lam1 lam2 : ℝ) (a b : ℝ)
    (_ha : 0 ≤ a) (_hb : 0 ≤ b) (hab : a + b = 1) :
    p.value (a * lam1 + b * lam2) = a * p.value lam1 + b * p.value lam2 := by
  unfold PathData.value
  have hconst : Real.log p.Q = a * Real.log p.Q + b * Real.log p.Q := by
    calc
      Real.log p.Q = (a + b) * Real.log p.Q := by rw [hab]; ring
      _ = a * Real.log p.Q + b * Real.log p.Q := by ring
  conv_lhs => rw [hconst]
  ring

/-- Per-path value is convex on all hazard rates. -/
theorem value_convexOn (p : PathData) : ConvexOn ℝ univ p.value := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simpa [smul_eq_mul] using le_of_eq (value_affine p x y a b ha hb hab)

/-- Per-path value is concave on all hazard rates. -/
theorem value_concaveOn (p : PathData) : ConcaveOn ℝ univ p.value := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    simpa [smul_eq_mul] using le_of_eq (value_affine p x y a b ha hb hab).symm

/-- Path action and path value are negatives of each other. -/
theorem action_neg_value (p : PathData) (lam : ℝ) :
    p.action lam = -(p.value lam) := by
  unfold PathData.action PathData.value
  ring

end TINProofs.C1

end
