/-
  C2 Part (iii): Poisson Limit

  This file pins down the Poisson crossover equation that the
  Binomial-to-Poisson limit must converge to.
-/
import TINProofs.C2.Defs
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm

open Finset BigOperators Nat
open scoped BigOperators
open Filter Topology

noncomputable section

/-- Lower Poisson tail through m. -/
def poissonLowerTail (mu : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ range (m + 1), poissonPMF mu j

/-- Upper Poisson tail from k onward. -/
def poissonUpperTail (mu : ℝ) (k : ℕ) : ℝ :=
  ∑' j : ℕ, if k ≤ j then poissonPMF mu j else 0

/-- Poisson crossover equation from the source theorem:
    P(X <= k - 2; mu) = P(X >= k; mu). -/
def poissonCrossoverCondition (k : ℕ) (mu : ℝ) : Prop :=
  poissonLowerTail mu (k - 2) = poissonUpperTail mu k

/-- Expanded form of the Poisson crossover condition. -/
theorem poissonCrossoverCondition_iff (k : ℕ) (mu : ℝ) :
    poissonCrossoverCondition k mu ↔
      (∑ j ∈ range (k - 2 + 1), poissonPMF mu j) =
        (∑' j : ℕ, if k ≤ j then poissonPMF mu j else 0) := by
  rfl

/-- Pointwise Binomial-to-Poisson convergence for the local real-valued PMF
    definitions. This is the law-of-small-numbers input for finite-tail
    convergence. -/
theorem binomialPMF_tendsto_poissonPMF (k : ℕ) {r : ℝ} {p : ℕ → ℝ}
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => binomialPMF n (p n) k) atTop (𝓝 (poissonPMF r k)) := by
  simpa [binomialPMF, poissonPMF] using
    ProbabilityTheory.tendsto_choose_mul_pow_of_tendsto_mul_atTop (p := p) (r := r) k hr

/-- Fixed finite lower tails converge termwise under the
    Binomial-to-Poisson scaling. -/
theorem binomialLowerTail_tendsto_poissonLowerTail (m : ℕ) {r : ℝ} {p : ℕ → ℝ}
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => ∑ j ∈ range (m + 1), binomialPMF n (p n) j)
      atTop (𝓝 (poissonLowerTail r m)) := by
  simpa [poissonLowerTail] using
    tendsto_finset_sum (range (m + 1))
      (fun j _hj => binomialPMF_tendsto_poissonPMF j hr)

/-- The local real-valued Binomial PMF sums to one over its finite support. -/
theorem binomialPMF_sum_range_eq_one (n : ℕ) (p : ℝ) :
    ∑ j ∈ range (n + 1), binomialPMF n p j = 1 := by
  have h := add_pow p (1 - p) n
  have hp : p + (1 - p) = (1 : ℝ) := by ring
  rw [hp, one_pow] at h
  rw [h]
  simp [binomialPMF, mul_assoc, mul_left_comm, mul_comm]

/-- Natural closed intervals as half-open intervals with a successor endpoint. -/
lemma Icc_eq_Ico_succ_nat (k n : ℕ) : Icc k n = Ico k (n + 1) := by
  ext j
  simp

/-- Binomial upper tails are complements of finite lower tails once the lower
    cutoff lies inside the finite support. -/
theorem binomialUpperTail_eq_one_sub_lower (n : ℕ) (p : ℝ) (k : ℕ)
    (hk : k ≤ n + 1) :
    binomialUpperTail n p k = 1 - ∑ j ∈ range k, binomialPMF n p j := by
  unfold binomialUpperTail
  rw [Icc_eq_Ico_succ_nat]
  have hsplit := sum_range_add_sum_Ico (fun j => binomialPMF n p j) hk
  have htotal := binomialPMF_sum_range_eq_one n p
  linarith

/-- The local real-valued Poisson PMF sums to one. -/
theorem hasSum_poissonPMF (mu : ℝ) : HasSum (fun j : ℕ => poissonPMF mu j) 1 := by
  have hs : HasSum (fun j : ℕ => mu ^ j / (j.factorial : ℝ)) (Real.exp mu) := by
    simpa [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp mu)
  have hs' := hs.mul_left (Real.exp (-mu))
  have hone : Real.exp (-mu) * Real.exp mu = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [← hone]
  simpa [poissonPMF, mul_div_assoc] using hs'

/-- Reindex a tail over `{j | k <= j}` as a sum over `i + k`. -/
theorem tsum_ite_ge_eq_nat_add (f : ℕ → ℝ) (k : ℕ) :
    (∑' j : ℕ, if k ≤ j then f j else 0) = ∑' i : ℕ, f (i + k) := by
  have hinj : Function.Injective (fun i : ℕ => i + k) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hsupport : Function.support (fun j : ℕ => if k ≤ j then f j else 0) ⊆
      Set.range (fun i : ℕ => i + k) := by
    intro j hj
    simp only [Function.mem_support] at hj
    by_cases hkj : k ≤ j
    · exact ⟨j - k, Nat.sub_add_cancel hkj⟩
    · simp [hkj] at hj
  have h := hinj.tsum_eq (f := fun j : ℕ => if k ≤ j then f j else 0) hsupport
  rw [← h]
  simp

/-- Poisson upper tails are complements of finite lower tails. -/
theorem poissonUpperTail_eq_one_sub_lower (mu : ℝ) (k : ℕ) :
    poissonUpperTail mu k = 1 - ∑ j ∈ range k, poissonPMF mu j := by
  unfold poissonUpperTail
  rw [tsum_ite_ge_eq_nat_add]
  have hs := hasSum_poissonPMF mu
  have hsplit := Summable.sum_add_tsum_nat_add k hs.summable
  have htotal := hs.tsum_eq
  linarith

/-- The zero-rate Poisson mass at zero. -/
theorem poissonPMF_zero_zero : poissonPMF 0 0 = 1 := by
  simp [poissonPMF]

/-- The zero-rate Poisson mass away from zero. -/
theorem poissonPMF_zero_of_pos (j : ℕ) (hj : 0 < j) : poissonPMF 0 j = 0 := by
  simp [poissonPMF, hj.ne']

/-- Any positive finite lower range contains the full zero-rate Poisson mass. -/
theorem sum_range_poissonPMF_zero_eq_one (k : ℕ) (hk : 0 < k) :
    ∑ j ∈ range k, poissonPMF 0 j = 1 := by
  rw [sum_eq_single 0]
  · exact poissonPMF_zero_zero
  · intro j hj hne
    apply poissonPMF_zero_of_pos
    omega
  · intro h0
    simp [hk] at h0

/-- At zero rate, every positive upper tail is zero. -/
theorem poissonUpperTail_zero_of_pos (k : ℕ) (hk : 0 < k) :
    poissonUpperTail 0 k = 0 := by
  rw [poissonUpperTail_eq_one_sub_lower, sum_range_poissonPMF_zero_eq_one k hk]
  norm_num

/-- At zero rate, every finite lower tail is one. -/
theorem poissonLowerTail_zero_eq_one (m : ℕ) :
    poissonLowerTail 0 m = 1 := by
  unfold poissonLowerTail
  apply sum_range_poissonPMF_zero_eq_one
  omega

/-- Fixed finite lower tails written with an exact `range k` cutoff converge
    termwise under the Binomial-to-Poisson scaling. -/
theorem binomialFiniteLowerTail_tendsto_poissonFiniteLowerTail
    (k : ℕ) {r : ℝ} {p : ℕ → ℝ}
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => ∑ j ∈ range k, binomialPMF n (p n) j)
      atTop (𝓝 (∑ j ∈ range k, poissonPMF r j)) := by
  exact tendsto_finset_sum (range k)
    (fun j _hj => binomialPMF_tendsto_poissonPMF j hr)

/-- Upper-tail convergence under the Binomial-to-Poisson scaling. -/
theorem binomialUpperTail_tendsto_poissonUpperTail
    (k : ℕ) {r : ℝ} {p : ℕ → ℝ}
    (hr : Tendsto (fun n => n * p n) atTop (𝓝 r)) :
    Tendsto (fun n => binomialUpperTail n (p n) k) atTop (𝓝 (poissonUpperTail r k)) := by
  have hEq : (fun n => binomialUpperTail n (p n) k) =ᶠ[atTop]
      (fun n => 1 - ∑ j ∈ range k, binomialPMF n (p n) j) := by
    filter_upwards [eventually_ge_atTop (k - 1)] with n hn
    rw [binomialUpperTail_eq_one_sub_lower]
    omega
  refine Tendsto.congr' hEq.symm ?_
  have hlim : Tendsto (fun n => (1 : ℝ) - ∑ j ∈ range k, binomialPMF n (p n) j)
      atTop (𝓝 ((1 : ℝ) - ∑ j ∈ range k, poissonPMF r j)) :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      (binomialFiniteLowerTail_tendsto_poissonFiniteLowerTail k hr)
  simpa [poissonUpperTail_eq_one_sub_lower] using hlim

/-- Continuity of each local Poisson PMF term. -/
theorem continuous_poissonPMF (j : ℕ) : Continuous fun mu : ℝ => poissonPMF mu j := by
  unfold poissonPMF
  fun_prop

/-- Continuity of finite Poisson lower tails. -/
theorem continuous_poissonLowerTail (m : ℕ) : Continuous fun mu : ℝ => poissonLowerTail mu m := by
  unfold poissonLowerTail
  exact continuous_finset_sum (range (m + 1)) (fun j _hj => continuous_poissonPMF j)

/-- Continuity of finite lower-tail sums with exact `range k` cutoffs. -/
theorem continuous_poissonFiniteLowerTail (k : ℕ) :
    Continuous fun mu : ℝ => ∑ j ∈ range k, poissonPMF mu j := by
  exact continuous_finset_sum (range k) (fun j _hj => continuous_poissonPMF j)

/-- Continuity of Poisson upper tails, via the finite complement identity. -/
theorem continuous_poissonUpperTail (k : ℕ) :
    Continuous fun mu : ℝ => poissonUpperTail mu k := by
  have hfun : (fun mu : ℝ => poissonUpperTail mu k) =
      fun mu : ℝ => 1 - ∑ j ∈ range k, poissonPMF mu j := by
    funext mu
    rw [poissonUpperTail_eq_one_sub_lower]
  rw [hfun]
  exact continuous_const.sub (continuous_poissonFiniteLowerTail k)

/-- IVT root-crossing theorem for any explicit bracket whose endpoints put
    the lower and upper Poisson tails on opposite sides. -/
theorem poissonCrossover_exists_of_bracket (k : ℕ) (a b : ℝ) (hab : a ≤ b)
    (ha : poissonUpperTail a k ≤ poissonLowerTail a (k - 2))
    (hb : poissonLowerTail b (k - 2) ≤ poissonUpperTail b k) :
    ∃ mu ∈ Set.Icc a b, poissonCrossoverCondition k mu := by
  have hcontU : ContinuousOn (fun mu : ℝ => poissonUpperTail mu k) (Set.Icc a b) :=
    (continuous_poissonUpperTail k).continuousOn
  have hcontL : ContinuousOn (fun mu : ℝ => poissonLowerTail mu (k - 2)) (Set.Icc a b) :=
    (continuous_poissonLowerTail (k - 2)).continuousOn
  obtain ⟨mu, hmu, hEq⟩ := IsPreconnected.intermediate_value₂
    (s := Set.Icc a b) isPreconnected_Icc
    (a := a) (b := b)
    (f := fun mu : ℝ => poissonUpperTail mu k)
    (g := fun mu : ℝ => poissonLowerTail mu (k - 2))
    (by simp [hab]) (by simp [hab]) hcontU hcontL ha hb
  exact ⟨mu, hmu, hEq.symm⟩

/-- Root-crossing existence from the zero-rate endpoint and any finite right
    endpoint where the Poisson tail inequality has reversed. -/
theorem poissonCrossover_exists_of_reverse_at (k : ℕ) (b : ℝ)
    (hk : 2 ≤ k) (hb0 : 0 ≤ b)
    (hb : poissonLowerTail b (k - 2) ≤ poissonUpperTail b k) :
    ∃ mu ∈ Set.Icc 0 b, poissonCrossoverCondition k mu := by
  apply poissonCrossover_exists_of_bracket k 0 b hb0
  · rw [poissonUpperTail_zero_of_pos k (by omega), poissonLowerTail_zero_eq_one (k - 2)]
    norm_num
  · exact hb

end
