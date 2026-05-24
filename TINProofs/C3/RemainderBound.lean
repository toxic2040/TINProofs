/-
  C3 Lemma 4: Taylor remainder contribution bound.
-/
import TINProofs.C3.Defs

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/-- Absolute bound for the nonlinear Lyapunov remainder term. -/
theorem remainder_abs_bound :
    |P.remainder| ≤ S.opNormA * S.M * P.rho ^ 3 :=
  P.remainderAbsBound

/-- One-sided form of the nonlinear remainder bound. -/
theorem remainder_upper_bound :
    P.remainder ≤ S.opNormA * S.M * P.rho ^ 3 :=
  le_trans (le_abs_self P.remainder) P.remainderAbsBound

end TINProofs.C3

end
