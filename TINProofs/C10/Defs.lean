/-
  C10: Fixed-Oracle Local Response -- definitions

  Source: discussion v0.9 Section 51.2

  Under a routing oracle O that is independent of hazard h,
  the retarded response kernel K_R(ell > 0) = 0. Route-state
  covariance N_AB(ell) can remain nontrivial, but this is
  autocorrelation, not causal response.

  This formally separates "looks like memory" from actual
  retarded causal response.
-/
import Mathlib

noncomputable section

namespace TINProofs.C10

/-- Scalar data for the fixed-oracle response theorem.

  The oracle O selects route state zeta_t from contact/availability
  information. The action A_t = A(zeta_t) is computed on the
  selected route. The key hypothesis is oracle independence:
  O does not depend on hazard h.
-/
structure OracleSetup where
  nStates : ℕ
  hnStates_pos : 0 < nStates

/--
An injection event: at time t, the oracle selects route state
zeta with action A(zeta). The hazard impulse delta_h at time t
can change the action at t but NOT the route selection at any
other time t' (oracle independence).
-/
structure InjectionEvent (O : OracleSetup) where
  action : ℝ
  haction_nonneg : 0 ≤ action

/--
A pair of injection events at times t and t+ell, for computing
the retarded response.
-/
structure EventPair (O : OracleSetup) where
  event_t : InjectionEvent O
  event_t_ell : InjectionEvent O
  lag : ℕ

/--
Oracle independence hypothesis: a hazard impulse at time t
does not change the route state at time t+ell for ell > 0.

Encoded as: the action at t+ell is unchanged by the impulse.
delta_action_t_ell = 0 when lag > 0.
-/
structure OracleIndependence (O : OracleSetup) (pair : EventPair O) where
  delta_action_t : ℝ
  delta_action_t_ell : ℝ
  h_local : pair.lag = 0 ∨ delta_action_t_ell = 0

end TINProofs.C10

end
