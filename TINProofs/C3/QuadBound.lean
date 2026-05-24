/-
  C3 Lemma 3: lower bound for the stabilizing quadratic term.
-/
import TINProofs.C3.Defs

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/-- The Lyapunov matrix quadratic form is bounded below by `q * rho^2`. -/
theorem quadratic_term_lower :
    S.q * P.rho ^ 2 ≤ P.quad :=
  P.quadLower

/-- The negative quadratic term is bounded above by `-q * rho^2`. -/
theorem negative_quadratic_term_upper :
    -P.quad ≤ -(S.q * P.rho ^ 2) :=
  neg_le_neg P.quadLower

end TINProofs.C3

end
