/-
  C9: S_T-eta Coupling Bound (discussion v0.9 Section 21.3)

  |Cov(S, eta | G)| <= sqrt(2 * I(S; eta | G))

  where S, eta in [0,1]. This is a Pinsker-type inequality for
  bounded random variables bounding how far infrastructure and
  routing efficiency can deviate from conditional independence.

  Also: Cauchy-Schwarz variance bound (Section 21.4):
    |Cov(S, eta | G)| <= sqrt(Var(S|G) * Var(eta|G))

  And: vanishing cases (Section 21.5):
    - Known infrastructure: Var(S|G) = 0 -> Cov = 0
    - Saturated routing: Var(eta|G) = 0 -> Cov = 0
-/
import TINProofs.C9.Defs

noncomputable section

namespace TINProofs.C9

/--
Pinsker coupling bound.

|Cov(S, eta | G)| <= sqrt(2 * MI(S; eta | G))

Trust boundary: Pinsker's inequality for bounded [0,1] random
variables. The sqrt(2) constant comes from the bounded range.
-/
theorem pinsker_coupling_bound (C : CouplingSetup)
    (h_pinsker : |C.covSEta| ^ 2 ≤ 2 * C.mi) :
    |C.covSEta| ≤ Real.sqrt (2 * C.mi) := by
  have h_rhs_nonneg : 0 ≤ 2 * C.mi := by
    nlinarith [C.hmi_nonneg]
  rw [Real.le_sqrt (abs_nonneg C.covSEta) h_rhs_nonneg]
  exact h_pinsker

/--
Cauchy-Schwarz variance bound.

|Cov(S, eta | G)| <= sqrt(Var(S|G) * Var(eta|G))

Directly computable from the existing dataset.
-/
theorem cauchy_schwarz_coupling_bound (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 ≤ C.varS * C.varEta) :
    |C.covSEta| ≤ Real.sqrt (C.varS * C.varEta) := by
  have h_rhs_nonneg : 0 ≤ C.varS * C.varEta :=
    mul_nonneg C.hvarS_nonneg C.hvarEta_nonneg
  rw [Real.le_sqrt (abs_nonneg C.covSEta) h_rhs_nonneg]
  simpa [sq_abs] using h_cs

/--
Vanishing case 1: known infrastructure.

If Var(S|G) = 0, then Cov(S, eta|G) = 0.
-/
theorem coupling_vanishes_known_infrastructure (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 ≤ C.varS * C.varEta)
    (h_varS_zero : C.varS = 0) :
    C.covSEta = 0 := by
  rw [h_varS_zero, zero_mul] at h_cs
  exact sq_eq_zero_iff.mp (le_antisymm h_cs (sq_nonneg C.covSEta))

/--
Vanishing case 2: saturated routing.

If Var(eta|G) = 0, then Cov(S, eta|G) = 0.
-/
theorem coupling_vanishes_saturated_routing (C : CouplingSetup)
    (h_cs : C.covSEta ^ 2 ≤ C.varS * C.varEta)
    (h_varEta_zero : C.varEta = 0) :
    C.covSEta = 0 := by
  rw [h_varEta_zero, mul_zero] at h_cs
  exact sq_eq_zero_iff.mp (le_antisymm h_cs (sq_nonneg C.covSEta))

/--
Decoupling criterion.

If MI(S; eta | G) = 0, then |Cov| = 0, so S and eta
are uncorrelated under G: separate optimization is exact.
-/
theorem decoupling_criterion (C : CouplingSetup)
    (h_pinsker : |C.covSEta| ^ 2 ≤ 2 * C.mi)
    (h_mi_zero : C.mi = 0) :
    C.covSEta = 0 := by
  rw [h_mi_zero, mul_zero] at h_pinsker
  have h_abs_zero : |C.covSEta| = 0 :=
    sq_eq_zero_iff.mp (le_antisymm h_pinsker (sq_nonneg (|C.covSEta|)))
  exact abs_eq_zero.mp h_abs_zero

end TINProofs.C9

end
