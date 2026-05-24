/-
  Paper-to-Lean cross-reference for TINProofs C1-C7.

  Each section quotes the manuscript theorem in natural language,
  then checks the corresponding Lean declaration. The #check commands
  verify that every referenced name still exists and has the expected
  type; if a theorem is renamed or removed, the build breaks here.

  Paper sources:
    C1  Theorem 6.3    (commodity hull, Legendre duality)
    C2  Theorem S2     (stochastic certification asymmetry)
    C3  Proposition C1 (Lyapunov radius of validity)
    C4  Lemma 2.6      (temporal transport factorization)
    C5  Proposition 2.7 (three-factor sparse law)
    C6  Theorem 1      (Ahlfors covering and volume scaling)
    C7  Theorem 2      (support failure via rate-distortion)
-/
import TINProofs.C1.Crossover
import TINProofs.C2.Absorbing
import TINProofs.C2.AsymmetryRatio
import TINProofs.C2.Expansion
import TINProofs.C2.GapTiers
import TINProofs.C3.RadiusOfValidity
import TINProofs.C4.BraessLocalization
import TINProofs.C5.ThreeFactor
import TINProofs.C5.ChainProperties
import TINProofs.C5.Classification
import TINProofs.C6.AhlforsCovering
import TINProofs.C7.SupportFailure

-- ═══════════════════════════════════════════════════════════════════
-- C1. Commodity Hull Theorem  (Theorem 6.3)
-- ═══════════════════════════════════════════════════════════════════

/- **Paper.** For a feasible path p = (T_p, Q_p), define
   A_p(λ) = −log Q_p + λ T_p.  For a, b ≥ 0 with a + b = 1,
   A_p(aλ₁ + bλ₂) = a A_p(λ₁) + b A_p(λ₂).

   **Lean.** `action_affine`: exact equality under convex combination,
   proved by `ring`. Corollaries derive `ConvexOn` and `ConcaveOn`. -/
#check @TINProofs.C1.action_affine
#check @TINProofs.C1.action_convexOn
#check @TINProofs.C1.action_concaveOn

/- **Paper.** V_p(λ) = log Q_p − λ T_p is likewise affine,
    and A_p(λ) = −V_p(λ).

    **Lean.** `value_affine` and `action_neg_value`. -/
#check @TINProofs.C1.value_affine
#check @TINProofs.C1.action_neg_value

/- **Paper.** The finite lower envelope F_C(λ) = inf_{p∈C} A_p(λ) is
    concave on ℝ; the upper envelope V_C(λ) = sup_{p∈C} V_p(λ) is convex;
    and V_C(λ) = −F_C(λ)  (Legendre duality).

    **Lean.** `support_concaveOn`, `valueFn_convexOn`, `legendre_duality`. -/
#check @TINProofs.C1.support_concaveOn
#check @TINProofs.C1.valueFn_convexOn
#check @TINProofs.C1.legendre_duality

/- **Paper.** For distinct exposures T_i ≠ T_j, set
    λ_{ij} = (log Q_j − log Q_i) / (T_j − T_i).
    Then A_i(λ_{ij}) = A_j(λ_{ij}).  If T_i < T_j then
    λ < λ_{ij}  ⟹  A_j(λ) < A_i(λ), and
    λ_{ij} < λ  ⟹  A_i(λ) < A_j(λ).

    **Lean.** `action_eq_at_crossover`, `action_lt_below_crossover`,
    `action_gt_above_crossover`. -/
#check @TINProofs.C1.action_eq_at_crossover
#check @TINProofs.C1.action_lt_below_crossover
#check @TINProofs.C1.action_gt_above_crossover


-- ═══════════════════════════════════════════════════════════════════
-- C2. Stochastic Certification Asymmetry  (Theorem S2)
-- ═══════════════════════════════════════════════════════════════════

/- **Paper, Part (i): Absorbing Lowest Tier.**
    Let x_i = ⌈kτ_i⌉.  If p ≥ 0 and np < kτ_i − 1, then ⌈np⌉ < x_i.
    Consequently any median m ≤ ⌈np⌉ also lies below the cutoff.

    **Lean.** `ceil_mean_lt_xMin_of_lt_sub_one`,
    `median_lt_xMin_of_median_le_ceil_mean`,
    `absorbing_lowest_tier_median_lt_cutoff`.
    The Binomial median upper bound (Kaas & Buhrman 1980) is an explicit
    hypothesis, not proved from first principles. -/
#check @ceil_mean_lt_xMin_of_lt_sub_one
#check @median_lt_xMin_of_median_le_ceil_mean
#check @absorbing_lowest_tier_median_lt_cutoff

/- **Paper, Part (ii): Tier Asymmetry as Finite Sums.**
    R_{T,T−} = Σ_{j=0}^{x_T−1} B_{n,p}(j) / Σ_{j=x_{T−}}^{n} B_{n,p}(j).

    **Lean.** `tierAsymmetryRatio_eq_binomial_sums`, after showing each
    cutoff x_i is positive via `TierSystem.xMin_pos`. -/
#check @TierSystem.xMin_pos
#check @tierAsymmetryRatio_eq_binomial_sums

/- **Paper, Part (iii): Binomial-to-Poisson Tail Limit.**
    If np_n → r, then B_{n,p_n}(k) → e^{−r} r^k / k!, and the
    finite lower and upper tails converge to Poisson tails.
    The limiting crossover equation is L_{k−2}(μ) = U_k(μ); by IVT,
    a root exists in any bracket where the tails swap dominance.

    **Lean.** `binomialPMF_tendsto_poissonPMF`,
    `binomialLowerTail_tendsto_poissonLowerTail`,
    `binomialUpperTail_tendsto_poissonUpperTail`,
    `poissonCrossover_exists_of_bracket`,
    `poissonCrossover_exists_of_reverse_at`. -/
#check @binomialPMF_tendsto_poissonPMF
#check @binomialLowerTail_tendsto_poissonLowerTail
#check @binomialUpperTail_tendsto_poissonUpperTail
#check @poissonCrossover_exists_of_bracket
#check @poissonCrossover_exists_of_reverse_at

/- **Paper, Part (iv): Asymptotic Delivery-Ratio Expansion.**
    Under the Adell-Jodra asymptotic input λ*_k = k − 5/6 + O(k⁻¹),
    the delivery ratio satisfies DR*_k = 1 − 5/(6k) + O(k⁻²).

    **Lean.** `drStar_expansion_of_lambda_expansion`, conditional on
    `adellJodraAsymptoticInput` (Adell & Jodra 2005). -/
#check @drStar_expansion_of_lambda_expansion

/- **Paper, Part (v): Gap Tiers.**
    If two adjacent ceiling cutoffs coincide, x_i = x_j,
    then no integer X satisfies x_i ≤ X < x_j.

    **Lean.** `gap_tier`. -/
#check @gap_tier


-- ═══════════════════════════════════════════════════════════════════
-- C3. Lyapunov Radius of Validity  (Proposition C1)
-- ═══════════════════════════════════════════════════════════════════

/- **Paper.** The Lyapunov quadratic satisfies
    α_min ρ² ≤ V ≤ α_max ρ².

    **Lean.** `eigen_sandwich_lower`, `eigen_sandwich_upper`,
    `eigen_sandwich`. -/
#check @TINProofs.C3.eigen_sandwich_lower
#check @TINProofs.C3.eigen_sandwich_upper
#check @TINProofs.C3.eigen_sandwich

/- **Paper.** The derivative decomposes as V̇ = −Q(δ) + R(δ), with
    qρ² ≤ Q(δ) and |R(δ)| ≤ ‖A‖Mρ³.  Combined:
    V̇ ≤ −qρ² + ‖A‖Mρ³.

    **Lean.** `vdot_decomposition`, `quadratic_term_lower`,
    `remainder_abs_bound`, `vdot_le_quadratic_plus_cubic`. -/
#check @TINProofs.C3.vdot_decomposition
#check @TINProofs.C3.quadratic_term_lower
#check @TINProofs.C3.remainder_abs_bound
#check @TINProofs.C3.vdot_le_quadratic_plus_cubic

/- **Paper.** Set r_* = min(r₀, q/(2‖A‖M)) and c_* = q/(2α_max).
    The radius r_* is positive.  If ρ < r_*, then V̇ ≤ −c_* V.

    **Lean.** `criticalRadius_pos`, `lyapunov_radius_of_validity`. -/
#check @TINProofs.C3.criticalRadius_pos
#check @TINProofs.C3.lyapunov_radius_of_validity

/- **Paper.** If V ≤ V₀ and V₀ < α_min r_*², then ρ < r_*.
    On the boundary V = V₀ of such a sublevel set, V̇ ≤ 0.

    **Lean.** `sublevel_inside_critical_ball`,
    `sublevel_boundary_vdot_nonpos`. -/
#check @TINProofs.C3.sublevel_inside_critical_ball
#check @TINProofs.C3.sublevel_boundary_vdot_nonpos


-- ═══════════════════════════════════════════════════════════════════
-- C4. Temporal Transport Factorization  (Lemma 2.6)
-- ═══════════════════════════════════════════════════════════════════

/- **Paper.** Let D ⊆ F be delivery and feasibility events.
    Then D ∩ Fᶜ = ∅, P(D ∩ Fᶜ) = 0, and P(D) ≤ P(F).

    **Lean.** `delivery_inter_infeasible_eq_empty`,
    `delivery_zero_when_infeasible`,
    `delivery_measure_le_feasible`. -/
#check @TINProofs.C4.delivery_inter_infeasible_eq_empty
#check @TINProofs.C4.delivery_zero_when_infeasible
#check @TINProofs.C4.delivery_measure_le_feasible

/- **Paper.** Whenever S_T ≠ 0, DR = S_T · η.

    **Lean.** `exact_factorization` (ENNReal),
    `exact_factorization_real` (ℝ). -/
#check @TINProofs.C4.exact_factorization
#check @TINProofs.C4.exact_factorization_real

/- **Paper.** For an augmentation F ⊆ F', S_T ≤ S'_T.

    **Lean.** `st_monotone`, `stReal_monotone`. -/
#check @TINProofs.C4.st_monotone
#check @TINProofs.C4.stReal_monotone

/- **Paper.** If an augmentation has S'_T > 0, preserves the measure,
    and DR' < DR, then η' < η.

    **Lean.** `braess_in_eta`, `braess_in_etaReal`. -/
#check @TINProofs.C4.braess_in_eta
#check @TINProofs.C4.braess_in_etaReal


-- ═══════════════════════════════════════════════════════════════════
-- C5. Three-Factor Sparse Law  (Proposition 2.7)
-- ═══════════════════════════════════════════════════════════════════

/- **Paper.** Define η_lyap = exp(E[H]·λ) and Φ = η / η_lyap.
    The sparse-law delivery ratio factors as DR = S_T · η_lyap · Φ.

    **Lean.** `three_factor`. -/
#check @TINProofs.C5.three_factor

/- **Paper.** η_lyap is strictly positive, and when E[H] > 0 and
    λ < 0, η_lyap < 1.  If η > 0 then Φ > 0.

    **Lean.** `etaLyap_pos`, `etaLyap_lt_one`, `phi_pos`. -/
#check @TINProofs.C5.etaLyap_pos
#check @TINProofs.C5.etaLyap_lt_one
#check @TINProofs.C5.phi_pos

/- **Paper.** For hop probabilities p_i ∈ (0,1) with n > 0,
    (1/n) Σ log p_i < 0.

    **Lean.** `lyapunov_exponent_neg`. -/
#check @TINProofs.C5.lyapunov_exponent_neg

/- **Paper.** For two residual measurements (Φ₁, E₁) and (Φ₂, E₂)
    with Φ > 0 and E₁ ≠ E₂, define
    γ = (log Φ₂ − log Φ₁) / (E₂ − E₁).
    γ < 0 is a trap; γ > 0 is a cluster.

    **Lean.** `morphologySlope`, `isTrap`, `isCluster`. -/
#check @TINProofs.C5.morphologySlope
#check @TINProofs.C5.isTrap
#check @TINProofs.C5.isCluster


-- ===================================================================
-- C6. Ahlfors Covering and Volume Scaling  (Theorem 1)
-- ===================================================================

/- **Paper.** Under Ahlfors gamma-regularity, the covering number
    N_U(epsilon) satisfies A1 |U| epsilon^{-gamma} <= N_U(epsilon)
    <= A2 |U| epsilon^{-gamma}, with A1 = 1/C2 and A2 = 2^gamma/C1.
    The packing-to-covering step is represented by the structural
    hypothesis N_U(epsilon) <= M.

    **Lean.** `covering_lower_bound`, `covering_upper_bound`,
    `ahlfors_covering`, `ansatz_validity`. -/
#check @TINProofs.C6.covering_lower_bound
#check @TINProofs.C6.covering_upper_bound
#check @TINProofs.C6.ahlfors_covering
#check @TINProofs.C6.ansatz_validity


-- ===================================================================
-- C7. Support Failure via Rate-Distortion  (Theorem 2)
-- ===================================================================

/- **Paper.** Under the Markov chain Y -> Z -> Y_hat and capacity
    bound I(Y;Z) <= C_b, achieving resolution eps requires
    R(eps) <= C_b. Below the threshold eps_star, no reconstruction
    achieves resolution eps.

    **Lean.** `support_necessary`, `support_failure`,
    `below_threshold_unsupportable`, `eps_star_le_eps_eff`. -/
#check @TINProofs.C7.support_necessary
#check @TINProofs.C7.support_failure
#check @TINProofs.C7.below_threshold_unsupportable
#check @TINProofs.C7.eps_star_le_eps_eff
