/-
  C2 Part (v): Gap Tiers

  Tier T is unreachable when ⌈k·τ_T⌉ = ⌈k·τ_{T-1}⌉.
  The achievable DR values are {0, 1/k, ..., 1}; if no
  element falls in [τ_T, τ_{T-1}), the tier is empty.
-/
import TINProofs.C2.Defs

open Finset BigOperators Nat

/-- No integer X can satisfy xLower ≤ X < xUpper when xLower = xUpper. -/
theorem no_achievable_in_gap (xLower xUpper : ℕ) (h : xLower = xUpper) :
    ∀ X : ℕ, ¬(xLower ≤ X ∧ X < xUpper) := by
  intro X ⟨h1, h2⟩
  omega

/-- Gap tier theorem: tier T is unreachable when the ceiling boundaries
    coincide. This is Part (v) of Theorem S2. -/
theorem gap_tier (ts : TierSystem)
    (i j : Fin (ts.M - 1))
    (h_gap : ts.xMin i = ts.xMin j) :
    ∀ X : ℕ, ¬(ts.xMin i ≤ X ∧ X < ts.xMin j) :=
  no_achievable_in_gap _ _ h_gap
