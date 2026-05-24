import TINProofs.C1.ActionAffine

open Real Set

noncomputable section

namespace TINProofs.C1

private theorem value_eq_neg_action (p : PathData) (lam : ℝ) :
    p.value lam = -(p.action lam) := by
  unfold PathData.action PathData.value
  ring

/-- The support function is concave: finite infimum of affine actions. -/
theorem support_concaveOn (ch : CommodityHull) :
    ConcaveOn ℝ univ ch.support := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    unfold CommodityHull.support
    simp only [smul_eq_mul]
    apply Finset.le_inf'
    intro p hp
    have hx : ch.paths.inf' ch.hnonempty (fun q => q.action x) ≤ p.action x :=
      Finset.inf'_le (s := ch.paths) (f := fun q => q.action x) hp
    have hy : ch.paths.inf' ch.hnonempty (fun q => q.action y) ≤ p.action y :=
      Finset.inf'_le (s := ch.paths) (f := fun q => q.action y) hp
    calc
      a * ch.paths.inf' ch.hnonempty (fun q => q.action x) +
          b * ch.paths.inf' ch.hnonempty (fun q => q.action y)
          ≤ a * p.action x + b * p.action y := by
            exact add_le_add (mul_le_mul_of_nonneg_left hx ha)
              (mul_le_mul_of_nonneg_left hy hb)
      _ = p.action (a * x + b * y) := (action_affine p x y a b ha hb hab).symm

/-- The value function is the negation of the support function. -/
theorem valueFn_eq_neg_support (ch : CommodityHull) (lam : ℝ) :
    ch.valueFn lam = -(ch.support lam) := by
  unfold CommodityHull.valueFn CommodityHull.support
  apply le_antisymm
  · apply Finset.sup'_le
    intro p hp
    have hInf : ch.paths.inf' ch.hnonempty (fun q => q.action lam) ≤ p.action lam :=
      Finset.inf'_le (s := ch.paths) (f := fun q => q.action lam) hp
    calc
      p.value lam = -p.action lam := value_eq_neg_action p lam
      _ ≤ -(ch.paths.inf' ch.hnonempty (fun q => q.action lam)) := neg_le_neg hInf
  · obtain ⟨p, hp, hp_le⟩ :=
      (Finset.inf'_le_iff (H := ch.hnonempty) (f := fun q => q.action lam)
        (a := ch.paths.inf' ch.hnonempty (fun q => q.action lam))).mp le_rfl
    have hToValue :
        -(ch.paths.inf' ch.hnonempty (fun q => q.action lam)) ≤ p.value lam := by
      calc
        -(ch.paths.inf' ch.hnonempty (fun q => q.action lam)) ≤ -p.action lam :=
          neg_le_neg hp_le
        _ = p.value lam := (value_eq_neg_action p lam).symm
    exact hToValue.trans (Finset.le_sup' (s := ch.paths) (f := fun q => q.value lam) hp)

/-- The value function is convex: finite supremum of affine values. -/
theorem valueFn_convexOn (ch : CommodityHull) :
    ConvexOn ℝ univ ch.valueFn := by
  constructor
  · exact convex_univ
  · intro x _hx y _hy a b ha hb hab
    unfold CommodityHull.valueFn
    simp only [smul_eq_mul]
    apply Finset.sup'_le
    intro p hp
    have hx : p.value x ≤ ch.paths.sup' ch.hnonempty (fun q => q.value x) :=
      Finset.le_sup' (s := ch.paths) (f := fun q => q.value x) hp
    have hy : p.value y ≤ ch.paths.sup' ch.hnonempty (fun q => q.value y) :=
      Finset.le_sup' (s := ch.paths) (f := fun q => q.value y) hp
    calc
      p.value (a * x + b * y) = a * p.value x + b * p.value y :=
        value_affine p x y a b ha hb hab
      _ ≤ a * ch.paths.sup' ch.hnonempty (fun q => q.value x) +
          b * ch.paths.sup' ch.hnonempty (fun q => q.value y) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hx ha)
              (mul_le_mul_of_nonneg_left hy hb)

end TINProofs.C1

end
