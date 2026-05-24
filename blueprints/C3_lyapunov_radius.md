# Blueprint C3: Lyapunov Radius of Validity (Proposition C1)

Source: `~/Desktop/Papers/sdtc/sntc_dr_decomposition.tex`, lines 121-140
Also: `~/Desktop/SNTCProject/docs/2026-05-14-phi-mesh-and-emj-theorems.md` (Prop C)

## Goal

Formalize the quadratic Lyapunov radius-of-validity proposition. Given a
smooth ODE, a diagonal positive weight matrix A, and a Taylor remainder
bound on the nonlinear term, prove that V(delta) = delta^T A delta decreases
exponentially inside a computable ball of radius r*.

This is classical dynamical systems / matrix analysis. No domain-specific
infrastructure needed.

---

## Mathematical Setup

Variables:
- n : ℕ (dimension, n = 4 in the paper but proof is general)
- A : Matrix (Fin n) (Fin n) ℝ, positive definite diagonal
- J : Matrix (Fin n) (Fin n) ℝ, Jacobian at equilibrium
- f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), smooth dynamics
- Phi_star : EuclideanSpace ℝ (Fin n), equilibrium (f(Phi_star) = 0)
- delta = Phi - Phi_star, perturbation
- R(delta) = f(Phi_star + delta) - J *v delta, nonlinear remainder

Definitions:
- V(delta) = delta^T A delta (quadratic Lyapunov function)
- Q = -(A^T J + J^T A) (Lyapunov matrix)
- q = lambda_min(Q) (minimum eigenvalue, assumed > 0)
- alpha_min = lambda_min(A), alpha_max = lambda_max(A)
- r_0, M : ℝ such that ||R(delta)|| <= (M/2) ||delta||^2 for ||delta|| <= r_0
- r* = min(r_0, q / (2 ||A||_op M))

Claim:
- On B(0, r*): V_dot <= -(q / (2 alpha_max)) V
- Sublevel sets {V <= V_0} with V_0 < alpha_min (r*)^2 are forward-invariant

---

## Proof Structure (5 lemmas + main theorem)

### Lemma 1: Eigenvalue sandwich for V

```
alpha_min * ||delta||^2 <= V(delta) <= alpha_max * ||delta||^2
```

Proof: V(delta) = delta^T A delta. Since A is positive definite with
eigenvalues in [alpha_min, alpha_max], this is the Rayleigh quotient bound.

Mathlib: `Matrix.PosDef`, `inner_mul_le_norm_mul_norm`, or direct from
eigenvalue characterization.

### Lemma 2: V_dot decomposition

```
V_dot = -delta^T Q delta + 2 delta^T A R(delta)
```

where V_dot = d/dt [delta^T A delta] along trajectories of delta_dot = J delta + R(delta).

Proof:
  V_dot = 2 delta^T A (delta_dot)
        = 2 delta^T A (J delta + R(delta))
        = 2 delta^T A J delta + 2 delta^T A R(delta)
        = delta^T (A J + J^T A) delta + 2 delta^T A R(delta)
        = -delta^T Q delta + 2 delta^T A R(delta)

The key step: 2 delta^T A J delta = delta^T (AJ + J^T A) delta because
(delta^T A J delta)^T = delta^T J^T A delta (scalar transpose = self),
so 2 delta^T A J delta = delta^T (AJ + J^T A) delta.

### Lemma 3: Quadratic term bound

```
delta^T Q delta >= q * ||delta||^2
```

Proof: q = lambda_min(Q) > 0 and Q is symmetric, so by the Rayleigh
quotient characterization.

Mathlib: For symmetric matrices, the minimum eigenvalue bounds the
quadratic form below. Search for `Matrix.IsHermitian.inner_mul_le` or
`Matrix.PosDef.inner_pos`.

### Lemma 4: Remainder bound via Cauchy-Schwarz

```
|2 delta^T A R(delta)| <= ||A||_op * M * ||delta||^3
```

Proof:
  |2 delta^T A R(delta)| <= 2 ||delta|| * ||A R(delta)||     (Cauchy-Schwarz)
                          <= 2 ||A||_op * ||delta|| * ||R(delta)||  (operator norm)
                          <= 2 ||A||_op * ||delta|| * (M/2) * ||delta||^2  (Taylor bound)
                          = ||A||_op * M * ||delta||^3

Mathlib:
- `inner_mul_le_norm_mul_norm` (Cauchy-Schwarz)
- `Matrix.norm_mul_vec_le` or `ContinuousLinearMap.le_opNorm` (operator norm)

### Lemma 5: V_dot bound on ball

```
For ||delta|| < r* = min(r_0, q/(2 ||A||_op M)):
  V_dot <= -(q/2) * ||delta||^2
```

Proof: From Lemmas 2-4:
  V_dot <= -q ||delta||^2 + ||A||_op M ||delta||^3
         = -||delta||^2 (q - ||A||_op M ||delta||)

When ||delta|| < q/(2 ||A||_op M):
  q - ||A||_op M ||delta|| > q - q/2 = q/2

So V_dot <= -(q/2) ||delta||^2.

### Main theorem: exponential V_dot bound

```
For ||delta|| < r*:
  V_dot <= -(q / (2 alpha_max)) * V
```

Proof: From Lemma 1, ||delta||^2 >= V / alpha_max.
Combined with Lemma 5: V_dot <= -(q/2)(V/alpha_max) = -(q/(2 alpha_max)) V.

### Corollary: forward invariance of sublevel sets

```
If V_0 < alpha_min * (r*)^2, then {V <= V_0} is forward-invariant.
```

Proof: On the boundary V = V_0, we have ||delta||^2 <= V_0/alpha_min < (r*)^2,
so ||delta|| < r*, so V_dot < 0. The flow cannot escape.

---

## Lean Formalization Strategy

### Key decision: work in finite dimensions with matrices

Use `EuclideanSpace ℝ (Fin n)` and `Matrix (Fin n) (Fin n) ℝ`.
The quadratic form V(delta) = delta^T A delta is `Matrix.dotProduct (A.mulVec delta) delta`
or equivalently `inner (A.toLin' delta) delta` depending on API.

### Recommended approach: state lemmas abstractly

Rather than building the full ODE infrastructure, state the theorem
conditionally. The key hypotheses are:

1. A is positive definite with eigenvalue bounds alpha_min, alpha_max
2. Q = -(A * J + J^T * A) has minimum eigenvalue q > 0
3. ||R(delta)|| <= (M/2) ||delta||^2 for ||delta|| <= r_0

The conclusion about V_dot follows algebraically from these.
We don't need to formalize the ODE solver or trajectory existence —
just that IF the dynamics satisfy delta_dot = J delta + R(delta),
THEN V_dot has the stated bound.

### File structure

```
TINProofs/
├── C3/
│   ├── Defs.lean           -- LyapunovSetup structure, V, Q, r_star
│   ├── EigenSandwich.lean  -- Lemma 1: alpha_min ||d||^2 <= V <= alpha_max ||d||^2
│   ├── VDotDecomp.lean     -- Lemma 2: V_dot = -d^T Q d + 2 d^T A R(d)
│   ├── QuadBound.lean      -- Lemma 3: d^T Q d >= q ||d||^2
│   ├── RemainderBound.lean -- Lemma 4: |2 d^T A R(d)| <= ||A|| M ||d||^3
│   ├── BallBound.lean      -- Lemma 5: V_dot <= -(q/2)||d||^2 on ball
│   └── RadiusOfValidity.lean -- Main theorem + forward invariance corollary
```

### Type definitions sketch

```lean
import Mathlib

open Matrix

variable {n : ℕ}

/-- Setup for the Lyapunov radius-of-validity proposition. -/
structure LyapunovSetup (n : ℕ) where
  A : Matrix (Fin n) (Fin n) ℝ
  J : Matrix (Fin n) (Fin n) ℝ
  hA_posDef : A.PosDef
  hA_diag : A.IsDiag  -- if this exists; otherwise encode as hypothesis
  alpha_min : ℝ
  alpha_max : ℝ
  h_alpha_min_pos : 0 < alpha_min
  h_alpha_max_pos : 0 < alpha_max
  h_alpha_bound : ∀ x : Fin n → ℝ,
    alpha_min * ‖x‖^2 ≤ dotProduct x (A.mulVec x) ∧
    dotProduct x (A.mulVec x) ≤ alpha_max * ‖x‖^2
  r_0 : ℝ
  hr_0 : 0 < r_0
  M_taylor : ℝ
  hM : 0 < M_taylor
  q : ℝ  -- min eigenvalue of Q = -(A^T J + J^T A)
  hq : 0 < q

/-- Quadratic Lyapunov function V(delta) = delta^T A delta. -/
noncomputable def lyapunovV (setup : LyapunovSetup n)
    (delta : Fin n → ℝ) : ℝ :=
  dotProduct delta (setup.A.mulVec delta)

/-- The Lyapunov matrix Q = -(A^T J + J^T A). -/
noncomputable def lyapunovQ (setup : LyapunovSetup n) :
    Matrix (Fin n) (Fin n) ℝ :=
  -(setup.A.transpose * setup.J + setup.J.transpose * setup.A)

/-- Critical radius r* = min(r_0, q / (2 ||A|| M)). -/
noncomputable def criticalRadius (setup : LyapunovSetup n) : ℝ :=
  min setup.r_0 (setup.q / (2 * ‖setup.A‖ * setup.M_taylor))
```

### Mathlib modules to search

For the matrix/linear algebra:
- `Mathlib.LinearAlgebra.Matrix.PosDef` -- positive definiteness
- `Mathlib.LinearAlgebra.Matrix.Hermitian` -- symmetric matrices
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse` -- invertibility
- `Mathlib.LinearAlgebra.Matrix.Spectrum` -- eigenvalues
- `Mathlib.Analysis.Matrix` -- matrix norms
- `Mathlib.Analysis.InnerProductSpace.Basic` -- inner products, Cauchy-Schwarz

For the Cauchy-Schwarz / norm bounds:
- `inner_mul_le_norm_mul_norm` -- |⟨x,y⟩| ≤ ‖x‖ ‖y‖
- `EuclideanSpace.norm_eq` -- ‖x‖ = sqrt(∑ x_i^2)
- `Matrix.norm_mulVec_le` -- ‖A x‖ ≤ ‖A‖ ‖x‖ (if operator norm exists)

For the quadratic form / eigenvalue:
- `Matrix.PosDef.inner_pos` or similar
- `Matrix.IsHermitian.eigenvalues` -- eigenvalue access
- The Rayleigh quotient characterization may need manual proof

### Known pitfalls

1. **Matrix norm in mathlib**: mathlib uses `‖A‖` for the operator norm
   induced by the Euclidean norm on Fin n → ℝ. Check if
   `NormedAddCommGroup` instance exists for `Matrix (Fin n) (Fin n) ℝ`.
   If not, use `Matrix.opNorm` or define it manually.

2. **Quadratic form vs bilinear form**: The expression `delta^T A delta`
   can be written as `Matrix.dotProduct delta (A.mulVec delta)` or via
   `BilinForm`. The `dotProduct` version is more explicit.

3. **Symmetric part**: The identity `2 x^T A J x = x^T (AJ + J^T A) x`
   requires showing that the scalar `x^T M x` equals `x^T M^T x` for
   any matrix M (since it's a 1x1 matrix = its transpose). This is
   `Matrix.dotProduct_mulVec_comm` or similar.

4. **Operator norm bound**: `‖A.mulVec x‖ ≤ ‖A‖ * ‖x‖` may need the
   `ContinuousLinearMap` bridge. Matrix to CLM conversion is in
   `Matrix.toLin'` and `Matrix.toContinuousLinearMap`.

5. **The min in r***: Use `min_le_left` and `min_le_right` to extract
   both bounds from `||delta|| < r*`.

### GPT workflow

1. Start with `Defs.lean` — get the types compiling. The `LyapunovSetup`
   structure may need adjustment depending on what mathlib provides for
   positive definite matrices and eigenvalue access.

2. `EigenSandwich.lean` — Lemma 1 may follow directly from the hypotheses
   in `LyapunovSetup` (the eigenvalue bounds are stated as hypotheses).
   If so, this file is thin.

3. `QuadBound.lean` — Lemma 3. Same pattern: q is stated as a hypothesis.
   The content is showing `dotProduct delta (Q.mulVec delta) >= q * ‖delta‖^2`.

4. `RemainderBound.lean` — Lemma 4. This is the meatiest file. Needs
   Cauchy-Schwarz and operator norm bound. If operator norm is hard, state
   `‖A.mulVec x‖ ≤ opNormA * ‖x‖` as a hypothesis and move on.

5. `BallBound.lean` — combines Lemmas 3 and 4. Mostly `linarith` / `nlinarith`.

6. `RadiusOfValidity.lean` — combines Lemma 5 with the eigenvalue sandwich.
   Should be short.

### Success criteria

- `lake build` passes with zero errors
- Main theorem has no `sorry`
- Acceptable `sorry` locations: if operator norm bound for matrices is
  unavailable in mathlib, state it as a hypothesis (honest boundary,
  same pattern as Adell-Jodra in C2)

### Alternative: fully hypothetical approach

If the matrix infrastructure proves too heavy, a clean alternative is to
state everything as real-variable inequalities with named hypotheses:

```lean
theorem lyapunov_radius_of_validity
    -- Eigenvalue hypotheses
    (alpha_min alpha_max q : ℝ)
    (h_alpha_pos : 0 < alpha_min) (h_alpha_max : alpha_min ≤ alpha_max)
    (hq : 0 < q)
    -- Taylor hypotheses
    (r_0 M_taylor : ℝ) (hr0 : 0 < r_0) (hM : 0 < M_taylor)
    (opNormA : ℝ) (hA : 0 < opNormA)
    -- Lyapunov function value and derivative
    (V Vdot norm_delta_sq : ℝ)
    -- Sandwich
    (h_lower : alpha_min * norm_delta_sq ≤ V)
    (h_upper : V ≤ alpha_max * norm_delta_sq)
    -- Vdot decomposition
    (h_Vdot : Vdot ≤ -q * norm_delta_sq + opNormA * M_taylor * norm_delta_sq ^ (3/2 : ℝ))
    -- Ball condition
    (h_ball : norm_delta_sq < (min r_0 (q / (2 * opNormA * M_taylor)))^2) :
    Vdot ≤ -(q / (2 * alpha_max)) * V := by
  sorry -- fill in
```

This captures the mathematical content without fighting mathlib's matrix API.
It's the "abstract events" approach applied to linear algebra. Valid and
publishable — the matrix API is plumbing, not mathematics.
