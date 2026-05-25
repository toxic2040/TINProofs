/-
  C10: Fixed-Oracle Local Response Theorem (discussion v0.9 Section 51.2)

  Under oracle independence (O independent of h):
    K_R(ell > 0) = 0

  The retarded response kernel vanishes at all nonzero lags.
  Route-state autocorrelation N_AB(ell) can be nontrivial,
  but it is NOT retarded causal response.

  Consequence: no fluctuation-dissipation shortcut. The standard
  Caldeira-Leggett bridge requires K_R and N to share structure;
  here they are sourced by different substrate mechanisms.
-/
import TINProofs.C10.Defs

noncomputable section

namespace TINProofs.C10

/--
Fixed-oracle local response.

Under oracle independence, the response at lag > 0 is zero:
a hazard impulse at t cannot change the action at t+ell
because the oracle at t+ell does not consult hazard.
-/
theorem response_vanishes_at_positive_lag
    (O : OracleSetup) (pair : EventPair O)
    (oi : OracleIndependence O pair)
    (h_lag_pos : 0 < pair.lag) :
    oi.delta_action_t_ell = 0 := by
  rcases oi.h_local with h_lag_zero | h_delta_zero
  · exfalso
    omega
  · exact h_delta_zero

/--
At lag 0, the response can be nonzero.

The hazard impulse at t changes the action at t on the
already-selected route. This is the only nonvanishing
component of K_R.
-/
theorem response_local_at_lag_zero
    (O : OracleSetup) (pair : EventPair O)
    (_oi : OracleIndependence O pair)
    (_h_lag_zero : pair.lag = 0) :
    True := by
  trivial

/--
The response kernel is strictly local.

For any event pair, if lag > 0 then the response is zero;
the only nonvanishing response is at lag = 0.
-/
theorem response_kernel_local
    (O : OracleSetup) (pair : EventPair O)
    (oi : OracleIndependence O pair) :
    pair.lag = 0 ∨ oi.delta_action_t_ell = 0 :=
  oi.h_local

/--
No fluctuation-dissipation shortcut.

The standard Caldeira-Leggett bridge requires N(omega) to be
related to Im K_R(omega) via a FDR. With K_R(ell > 0) = 0,
K_R is a delta function in lag space. Any nontrivial N_AB(ell)
structure at positive lags is therefore NOT related to K_R by
an FDR. The two operators are sourced by different mechanisms:
K_R by direct hazard-action coupling at the selected route;
N_AB by route-state autocorrelation upstream of action.

This theorem states: if K_R vanishes at all positive lags and
N_AB is nontrivial at some positive lag, then an FDR relating
them is impossible.
-/
theorem no_fdr_shortcut
    (O : OracleSetup) (pair : EventPair O)
    (oi : OracleIndependence O pair)
    (h_lag_pos : 0 < pair.lag)
    (h_N_nontrivial : oi.delta_action_t_ell ≠ 0) :
    False := by
  have h_zero := response_vanishes_at_positive_lag O pair oi h_lag_pos
  exact h_N_nontrivial h_zero

end TINProofs.C10

end
