import TINProofs.C1.SupportConcave

open Real Set

noncomputable section

namespace TINProofs.C1

/-- At the crossover slope, two paths have equal action. -/
theorem action_eq_at_crossover (pi pj : PathData) (hT : pi.T ≠ pj.T) :
    pi.action (crossoverSlope pi pj hT) = pj.action (crossoverSlope pi pj hT) := by
  unfold PathData.action crossoverSlope
  have hden : pj.T - pi.T ≠ 0 := sub_ne_zero.mpr hT.symm
  field_simp [hden]
  ring

/-- Below the crossover slope, the higher-exposure path has lower action. -/
theorem action_lt_below_crossover (pi pj : PathData) (hT : pi.T < pj.T)
    (lam : ℝ) (hlam : lam < crossoverSlope pi pj (ne_of_lt hT)) :
    pj.action lam < pi.action lam := by
  unfold PathData.action crossoverSlope at *
  have hden_pos : 0 < pj.T - pi.T := sub_pos.mpr hT
  have hmul : lam * (pj.T - pi.T) < Real.log pj.Q - Real.log pi.Q :=
    (lt_div_iff₀ hden_pos).mp hlam
  nlinarith

/-- Above the crossover slope, the lower-exposure path has lower action. -/
theorem action_gt_above_crossover (pi pj : PathData) (hT : pi.T < pj.T)
    (lam : ℝ) (hlam : crossoverSlope pi pj (ne_of_lt hT) < lam) :
    pi.action lam < pj.action lam := by
  unfold PathData.action crossoverSlope at *
  have hden_pos : 0 < pj.T - pi.T := sub_pos.mpr hT
  have hmul : Real.log pj.Q - Real.log pi.Q < lam * (pj.T - pi.T) :=
    (div_lt_iff₀ hden_pos).mp hlam
  nlinarith

/-- Finite-path Legendre duality as the definitional relationship `V = -F`. -/
theorem legendre_duality (ch : CommodityHull) (lam : ℝ) :
    ch.valueFn lam = -(ch.support lam) :=
  valueFn_eq_neg_support ch lam

end TINProofs.C1

end
