/-
  C3 Lemma 2: decomposition of the Lyapunov derivative.
-/
import TINProofs.C3.Defs

noncomputable section

namespace TINProofs.C3

variable {S : LyapunovSetup} (P : LyapunovPoint S)

/--
Pointwise derivative decomposition:
`Vdot = -delta^T Q delta + 2 delta^T A R(delta)`.
-/
theorem vdot_decomposition :
    P.Vdot = -P.quad + P.remainder :=
  P.vdotDecomp

end TINProofs.C3

end
