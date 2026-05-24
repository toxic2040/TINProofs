/-
  C2 Part (iv): Asymptotic Expansion

  The external Poisson-median asymptotic input is kept as a named
  hypothesis. This file proves the algebraic step from the lambda-star
  expansion to the delivery-ratio expansion.
-/
import TINProofs.C2.PoissonLimit

open Filter Topology Asymptotics

noncomputable section

/-- The asymptotic inverse of the reserve-cycle count. -/
def invK (k : ℕ) : ℝ :=
  ((k : ℝ)⁻¹)

/-- The `1 / k^2` scale used for the delivery-ratio remainder. -/
def invKSq (k : ℕ) : ℝ :=
  invK k ^ 2

/-- Center term for the Poisson crossover expansion:
    `lambda* = k - 5/6 + O(1/k)`. -/
def lambdaCenter (k : ℕ) : ℝ :=
  (k : ℝ) - (5 / 6 : ℝ)

/-- Delivery ratio induced by a selected Poisson crossover sequence. -/
def drStar (lambdaStar : ℕ → ℝ) (k : ℕ) : ℝ :=
  lambdaStar k / (k : ℝ)

/-- Target delivery-ratio expansion center: `1 - 5/(6k)`. -/
def drTarget (k : ℕ) : ℝ :=
  1 - (5 / 6 : ℝ) / (k : ℝ)

/-- A sequence selects Poisson crossover roots for all sufficiently large k. -/
def selectsPoissonCrossover (lambdaStar : ℕ → ℝ) : Prop :=
  ∀ᶠ k in atTop, poissonCrossoverCondition k (lambdaStar k)

/-- Named external input corresponding to the Poisson-median asymptotics:
    `lambda* = k - 5/6 + O(1/k)`. -/
def adellJodraAsymptoticInput (lambdaStar : ℕ → ℝ) : Prop :=
  (fun k : ℕ => lambdaStar k - lambdaCenter k) =O[atTop] invK

/-- Part (iv), conditional on the external Poisson-median asymptotic input:
    dividing `lambda* = k - 5/6 + O(1/k)` by k gives
    `DR* = 1 - 5/(6k) + O(1/k^2)`. -/
theorem drStar_expansion_of_lambda_expansion (lambdaStar : ℕ → ℝ)
    (_hCross : selectsPoissonCrossover lambdaStar)
    (hLam : adellJodraAsymptoticInput lambdaStar) :
    (fun k : ℕ => drStar lambdaStar k - drTarget k) =O[atTop] invKSq := by
  have hmul : (fun k : ℕ => (lambdaStar k - lambdaCenter k) * invK k) =O[atTop]
      (fun k : ℕ => invK k * invK k) :=
    hLam.mul (isBigO_refl invK atTop)
  refine hmul.congr' ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with k hk
    unfold drStar drTarget lambdaCenter invK
    have hk0 : (k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hk)
    field_simp [hk0]
  · exact Eventually.of_forall (fun k => by simp [invKSq, pow_two])

end
