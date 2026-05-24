/-
  C2: Stochastic Certification Asymmetry — Definitions

  Formalizes the tier system and Binomial delivery ratio
  from Theorem S2 (stochastic_certification.tex).
-/
import Mathlib

open Finset BigOperators Nat Real

noncomputable section

/-- A tier classification system with M tiers and M-1 thresholds. -/
structure TierSystem where
  M : ℕ
  hM : 2 ≤ M
  k : ℕ
  hk : 0 < k
  τ : Fin (M - 1) → ℝ
  hτ_pos : ∀ i, 0 < τ i
  hτ_lt_one : ∀ i, τ i < 1
  hτ_strict_anti : StrictAnti τ

/-- Delivery ratio: DR = min(X/k, 1). -/
def deliveryRatio (k : ℕ) (X : ℕ) : ℝ :=
  min ((X : ℝ) / (k : ℝ)) 1

/-- Minimum integer X that achieves tier i: x_i = ⌈k · τ_i⌉. -/
def TierSystem.xMin (ts : TierSystem) (i : Fin (ts.M - 1)) : ℕ :=
  ⌈(ts.k : ℝ) * ts.τ i⌉₊

/-- Binomial probability mass function: P(X = j) for X ~ Binom(n, p). -/
def binomialPMF (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

/-- Binomial CDF: P(X ≤ m) for X ~ Binom(n, p). -/
def binomialCDF (n : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1), binomialPMF n p j

/-- Upper tail: P(X ≥ m) for X ~ Binom(n, p). -/
def binomialUpperTail (n : ℕ) (p : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Icc m n, binomialPMF n p j

/-- The asymmetry ratio R_T: ratio of downgrade to upgrade probability.
    R_T = P(X ≤ x_T - 1) / P(X ≥ x_{T-1}) -/
def asymmetryRatio (n : ℕ) (p : ℝ) (xLower xUpper : ℕ) : ℝ :=
  binomialCDF n p (xLower - 1) / binomialUpperTail n p xUpper

/-- Poisson PMF: P(X = j) for X ~ Pois(mu). -/
def poissonPMF (mu : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-mu) * mu ^ j / (j.factorial : ℝ)

/-- The set of achievable DR values: {0, 1/k, 2/k, ..., 1}. -/
def achievableDR (k : ℕ) : Finset ℝ :=
  (range (k + 1)).image (fun (i : ℕ) => (i : ℝ) / (k : ℝ))

end
