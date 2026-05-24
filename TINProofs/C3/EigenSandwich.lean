/-
  C3 Lemma 1: eigenvalue sandwich for the quadratic Lyapunov value.
-/
import TINProofs.C3.Defs

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/-- Lower Rayleigh-quotient bound for the Lyapunov quadratic form. -/
theorem eigen_sandwich_lower :
    S.alphaMin * P.rho ^ 2 ≤ P.V :=
  P.eigenSandwich.1

/-- Upper Rayleigh-quotient bound for the Lyapunov quadratic form. -/
theorem eigen_sandwich_upper :
    P.V ≤ S.alphaMax * P.rho ^ 2 :=
  P.eigenSandwich.2

/-- The full Lyapunov eigenvalue sandwich. -/
theorem eigen_sandwich :
    S.alphaMin * P.rho ^ 2 ≤ P.V ∧ P.V ≤ S.alphaMax * P.rho ^ 2 :=
  P.eigenSandwich

end TINProofs.C3

end
