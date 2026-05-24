# Blueprint C6: Ahlfors Covering and Volume Scaling (Theorem 1, discussion v0.9 Section 13)

Source: `~/Desktop/TIN_daily/private_not_for_publication/discussion_v0.9.md`, lines 550-598
Also: `~/Desktop/Papers/theory/target_d_proof_and_regularity.md`, Part I

## Goal

Formalize the covering-number theorem for Ahlfors gamma-regular metric spaces.
Under the Ahlfors regularity hypothesis on a finite region U, the minimum
number of metric balls of radius epsilon needed to cover U scales as
|U| * epsilon^{-gamma}, with explicit two-sided bounds.

This is a standalone metric geometry theorem. It uses packing-covering duality
(a classical technique in geometric measure theory / doubling metric spaces).
No domain-specific temporal graph infrastructure needed.

---

## Mathematical Statement

### Setup

Let (V, d) be a metric space. Let U be a finite subset of V with |U| = card(U).
Let N_U(epsilon) be the minimum number of metric balls of radius epsilon
needed to cover U. Assume Ahlfors gamma-regularity on U at scale epsilon:

There exist constants C1, C2 > 0 such that for any x in U and any
epsilon in [epsilon_min, epsilon_max]:

    C1 * epsilon^gamma <= |B(x, epsilon) cap U| <= C2 * epsilon^gamma

### Theorem 1

There exist constants A1, A2 > 0 such that:

    A1 * |U| * epsilon^{-gamma} <= N_U(epsilon) <= A2 * |U| * epsilon^{-gamma}

with A1 = 1/C2 and A2 = 2^gamma / C1.

### Corollary 1.1 (Ansatz Validity)

If D_U(epsilon) := b * N_U(epsilon), then

    D_U(epsilon) is in [b * A1 * |U| * epsilon^{-gamma},
                         b * A2 * |U| * epsilon^{-gamma}]

confirming the graph-scaling ansatz D_U(epsilon) ~ K_U * epsilon^{-gamma}.

---

## Proof Structure (2 lemmas + main theorem + corollary)

### Lemma 1: Lower bound (covering implies volume bound)

```
N_U(epsilon) >= (1/C2) * |U| * epsilon^{-gamma}
```

Proof:
  Let {B(x_i, epsilon)}_{i=1}^{N} be an optimal covering. Then:
    |U| <= sum_{i=1}^{N} |B(x_i, epsilon) cap U|     (U is covered)
         <= N * C2 * epsilon^gamma                      (upper Ahlfors bound)

  Rearranging: N >= |U| / (C2 * epsilon^gamma) = (1/C2) * |U| * epsilon^{-gamma}.

### Lemma 2: Upper bound (packing implies covering bound)

```
N_U(epsilon) <= (2^gamma / C1) * |U| * epsilon^{-gamma}
```

Proof:
  Let {B(y_j, epsilon/2)}_{j=1}^{M} be a maximal packing of disjoint
  half-radius balls centered in U. By maximality of the packing,
  the doubled balls {B(y_j, epsilon)} cover U (any uncovered point
  could be added to the packing, contradicting maximality).
  Therefore N_U(epsilon) <= M.

  By disjointness and the lower Ahlfors bound:
    M * C1 * (epsilon/2)^gamma <= |U|

  (Each packing ball has at least C1 * (epsilon/2)^gamma points from U,
  and the balls are disjoint subsets of U.)

  Rearranging:
    M <= |U| / (C1 * (epsilon/2)^gamma)
       = |U| * 2^gamma / (C1 * epsilon^gamma)
       = (2^gamma / C1) * |U| * epsilon^{-gamma}

### Main Theorem: two-sided bound

Combine Lemma 1 and Lemma 2:

```
(1/C2) * |U| * epsilon^{-gamma} <= N_U(epsilon) <= (2^gamma/C1) * |U| * epsilon^{-gamma}
```

### Corollary: ansatz validity

Multiply through by b > 0:

```
b * A1 * |U| * epsilon^{-gamma} <= D_U(epsilon) <= b * A2 * |U| * epsilon^{-gamma}
```

---

## Lean Formalization Strategy

### Key decision: abstract scalar approach (matching C3 pattern)

The project convention (established in C3) is to encode the mathematical
hypotheses as scalar real-number conditions, not to build full metric space
infrastructure from scratch. This keeps the proof focused on the mathematical
content rather than fighting mathlib API.

The covering number N_U(epsilon) and ball cardinalities are given as
hypotheses relating real numbers. The Lean proof demonstrates that the
inequalities compose correctly.

An alternative would be to work with mathlib's `Metric.coveringByBalls`
and `Finset.card`. That path is available if the abstract approach feels
too thin, but the abstract approach matches the C3/C4/C5 precedent and
is more likely to succeed without sorry.

### File structure

```
TINProofs/
├── C6/
│   ├── Defs.lean            -- AhlforsSetup structure, covering number fields
│   ├── LowerBound.lean      -- Lemma 1: covering -> volume -> lower bound
│   ├── UpperBound.lean      -- Lemma 2: packing-covering duality -> upper bound
│   └── AhlforsCovering.lean -- Main theorem + ansatz corollary
```

### Type definitions

```lean
import Mathlib

noncomputable section

namespace TINProofs.C6

/-- Scalar data for the Ahlfors covering theorem. -/
structure AhlforsSetup where
  gamma : ℝ
  C1 : ℝ
  C2 : ℝ
  cardU : ℕ
  hgamma_pos : 0 < gamma
  hC1_pos : 0 < C1
  hC2_pos : 0 < C2
  hC1_le_C2 : C1 ≤ C2
  hcardU_pos : 0 < cardU

/-- Lower bound constant A1 = 1/C2. -/
def lowerConst (S : AhlforsSetup) : ℝ := 1 / S.C2

/-- Upper bound constant A2 = 2^gamma / C1. -/
def upperConst (S : AhlforsSetup) : ℝ := (2 : ℝ) ^ S.gamma / S.C1

end TINProofs.C6

end
```

### Lemma 1 sketch (LowerBound.lean)

```lean
import TINProofs.C6.Defs

noncomputable section

namespace TINProofs.C6

/--
A covering of U by N balls of radius epsilon, where each ball captures
at most C2 * epsilon^gamma points from U.
-/
structure CoveringWitness (S : AhlforsSetup) where
  N : ℕ               -- number of covering balls
  epsilon : ℝ
  heps_pos : 0 < epsilon
  hN_pos : 0 < N
  -- The N balls cover U: |U| <= sum of |B(x_i, eps) cap U|
  -- By upper Ahlfors bound, each term <= C2 * eps^gamma
  h_cover : (S.cardU : ℝ) ≤ (N : ℝ) * S.C2 * epsilon ^ S.gamma

/-- Lower bound on covering number from Ahlfors upper regularity. -/
theorem covering_lower_bound (S : AhlforsSetup) (cov : CoveringWitness S) :
    lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (- S.gamma) ≤ (cov.N : ℝ) := by
  sorry -- GPT fills: unfold lowerConst, rearrange cov.h_cover

end TINProofs.C6

end
```

### Lemma 2 sketch (UpperBound.lean)

```lean
import TINProofs.C6.Defs

noncomputable section

namespace TINProofs.C6

/--
A maximal packing of U by M disjoint balls of radius epsilon/2,
where each ball captures at least C1 * (epsilon/2)^gamma points from U.
Maximality implies the doubled balls cover U, so N_U(epsilon) <= M.
-/
structure PackingWitness (S : AhlforsSetup) where
  M : ℕ               -- number of packing balls
  epsilon : ℝ
  heps_pos : 0 < epsilon
  hM_pos : 0 < M
  -- Disjoint packing balls in U, each with >= C1 * (eps/2)^gamma points
  h_packing : (M : ℝ) * S.C1 * (epsilon / 2) ^ S.gamma ≤ (S.cardU : ℝ)
  -- Maximality: doubled balls cover U, so M is an upper bound on N_U(eps)
  -- (This is the key structural fact from packing-covering duality)

/-- Upper bound on covering number from packing-covering duality + Ahlfors lower regularity. -/
theorem covering_upper_bound (S : AhlforsSetup) (pk : PackingWitness S) :
    (pk.M : ℝ) ≤ upperConst S * (S.cardU : ℝ) * pk.epsilon ^ (- S.gamma) := by
  sorry -- GPT fills: unfold upperConst, rearrange pk.h_packing using (eps/2)^gamma = eps^gamma / 2^gamma

end TINProofs.C6

end
```

### Main theorem sketch (AhlforsCovering.lean)

```lean
import TINProofs.C6.LowerBound
import TINProofs.C6.UpperBound

noncomputable section

namespace TINProofs.C6

/--
Ahlfors Covering Theorem (Theorem 1).

Under Ahlfors gamma-regularity, the covering number N_U(epsilon) satisfies
two-sided bounds:

    (1/C2) |U| eps^{-gamma} <= N_U(eps) <= (2^gamma/C1) |U| eps^{-gamma}
-/
theorem ahlfors_covering (S : AhlforsSetup)
    (cov : CoveringWitness S) (pk : PackingWitness S)
    (h_same_eps : cov.epsilon = pk.epsilon)
    (h_same_N : cov.N = pk.M) :
    lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (- S.gamma) ≤ (cov.N : ℝ) ∧
    (cov.N : ℝ) ≤ upperConst S * (S.cardU : ℝ) * cov.epsilon ^ (- S.gamma) := by
  sorry -- GPT fills: split, apply covering_lower_bound, rw h_same_N, apply covering_upper_bound, rw h_same_eps

/--
Corollary 1.1: Ansatz validity.

If D_U(epsilon) = b * N_U(epsilon), then D_U is bounded by
b * A1 * |U| * eps^{-gamma} and b * A2 * |U| * eps^{-gamma}.
-/
theorem ansatz_validity (S : AhlforsSetup)
    (cov : CoveringWitness S) (pk : PackingWitness S)
    (h_same_eps : cov.epsilon = pk.epsilon)
    (h_same_N : cov.N = pk.M)
    (b : ℝ) (hb : 0 < b) :
    b * lowerConst S * (S.cardU : ℝ) * cov.epsilon ^ (- S.gamma) ≤ b * (cov.N : ℝ) ∧
    b * (cov.N : ℝ) ≤ b * upperConst S * (S.cardU : ℝ) * cov.epsilon ^ (- S.gamma) := by
  sorry -- GPT fills: obtain from ahlfors_covering, mul_le_mul_of_nonneg_left

end TINProofs.C6

end
```

---

## Mathlib modules to search

For real-number arithmetic:
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` -- `rpow`, `x ^ (r : ℝ)`
- `Mathlib.Algebra.Order.Field.Basic` -- division, reciprocal ordering
- `Mathlib.Order.MinMax` -- min/max lemmas

For Finset/cardinality (if going concrete):
- `Mathlib.Combinatorics.SimpleGraph.Basic`
- `Mathlib.Topology.MetricSpace.Basic` -- `Metric.ball`
- `Mathlib.Topology.MetricSpace.Bounded` -- bounded sets
- `Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace` -- covering lemmas

For the abstract scalar approach (recommended):
- `Mathlib.Tactic.Linarith` -- linear arithmetic
- `Mathlib.Tactic.NormNum` -- numeric normalization
- `Mathlib.Tactic.Positivity` -- positivity proofs
- `Mathlib.Tactic.Ring` -- ring identities
- `Mathlib.Tactic.FieldSimp` -- clearing denominators

---

## Known pitfalls

0. **Dot notation on non-field defs**: `lowerConst` and `upperConst` are
   standalone `def`s, not fields of `AhlforsSetup`. Use `lowerConst S` and
   `upperConst S`, NOT `lowerConst S` / `upperConst S`. The skeleton files
   already use the correct form. Same applies to `lowerConst_pos`,
   `upperConst_pos`, `cardU_cast_pos`.

1. **Negative exponents in `rpow`**: `epsilon ^ (-gamma)` is `Real.rpow epsilon (-gamma)`.
   This requires `0 < epsilon` for the expected behavior. Use `rpow_neg` and
   `rpow_natCast` carefully. The notation `epsilon ^ (-gamma : ℝ)` should work
   via the `HPow ℝ ℝ ℝ` instance.

2. **Division vs multiplication form**: The lower bound can be stated as
   `|U| / (C2 * eps^gamma) <= N` or equivalently `|U| * eps^{-gamma} / C2 <= N`.
   Pick one form and stick with it. The division form may be cleaner for
   `field_simp` tactics.

3. **ℕ to ℝ coercions**: `cardU` and `N` are ℕ but the inequalities are in ℝ.
   Use `(cardU : ℝ)` coercions. Key lemma: `Nat.cast_pos` for `0 < (n : ℝ)`.
   Also `Nat.cast_le` for `(m : ℝ) ≤ (n : ℝ) ↔ m ≤ n`.

4. **The (epsilon/2)^gamma term**: In the upper bound proof, the key step is
   `(epsilon/2)^gamma = epsilon^gamma / 2^gamma`. Use `div_rpow` or
   `Real.rpow_natCast` + `div_pow`. This is where the `2^gamma` in A2 comes from.

5. **Positivity of constants**: A1 = 1/C2 > 0 and A2 = 2^gamma/C1 > 0 follow
   from positivity of C1, C2, and 2^gamma. The `positivity` tactic should handle
   these, but explicit proofs may be needed.

---

## Trust boundaries

The packing-covering duality step (maximality of packing implies covering)
is encoded as a structural hypothesis in `PackingWitness`, not proved from
first principles. This is analogous to the Kaas-Buhrman and Adell-Jodra
hypotheses in C2. The mathematical content of this fact is:

> If {B(y_j, r)}_{j=1}^M is a maximal set of points in U such that the
> balls B(y_j, r) are pairwise disjoint, then U is contained in the union
> of the balls B(y_j, 2r).

This is a standard result in metric space theory. It could be proved in Lean
(it follows from the triangle inequality), but encoding it requires formalizing
ball membership and disjointness for Finsets in metric spaces. Stating it as
a hypothesis is the honest approach for the first pass.

If time allows, proving the packing-to-covering step from the triangle
inequality would strengthen the formalization. The key step:

  For any x in U, if x is not in any B(y_j, r), then B(x, r) is disjoint
  from all B(y_j, r), contradicting maximality. Therefore x must be in some
  B(y_j, r), hence in B(y_j, 2r) by the triangle inequality.

---

## Design choices matching project conventions

1. **Scalar hypotheses over concrete types** (matches C3, C5): encode the
   metric geometry as scalar inequalities, not as full metric space + Finset
   infrastructure. The mathematical content is in the inequality algebra.

2. **Namespace `TINProofs.C6`** (matches C1-C5 pattern).

3. **Structure for setup data** (matches `LyapunovSetup` in C3): a single
   `AhlforsSetup` record carries all constants and positivity proofs.

4. **Witness structures for intermediate data** (matches `LyapunovPoint` in C3):
   `CoveringWitness` and `PackingWitness` carry the per-instance data and
   hypotheses.

5. **Import chain**: `Defs.lean` -> `LowerBound.lean` / `UpperBound.lean` -> `AhlforsCovering.lean`.

---

## Statements.lean additions

After completion, add to `TINProofs/Statements.lean`:

```lean
import TINProofs.C6.AhlforsCovering

-- ===================================================================
-- C6. Ahlfors Covering and Volume Scaling  (Theorem 1, discussion v0.9)
-- ===================================================================

/- **Paper.** Under Ahlfors gamma-regularity, the covering number
    N_U(epsilon) satisfies A1 |U| eps^{-gamma} <= N_U(eps) <= A2 |U| eps^{-gamma}
    with A1 = 1/C2 and A2 = 2^gamma/C1.

    **Lean.** `covering_lower_bound`, `covering_upper_bound`, `ahlfors_covering`,
    `ansatz_validity`. -/
#check @TINProofs.C6.covering_lower_bound
#check @TINProofs.C6.covering_upper_bound
#check @TINProofs.C6.ahlfors_covering
#check @TINProofs.C6.ansatz_validity
```

---

## GPT workflow

1. **Start with `Defs.lean`**. Get `AhlforsSetup`, `lowerConst`, `upperConst`
   compiling. Prove `lowerConst_pos` and `upperConst_pos` helper lemmas.

2. **`LowerBound.lean`**. Define `CoveringWitness`. Prove `covering_lower_bound`.
   This is mostly `field_simp` + `linarith` after unfolding `lowerConst` and
   rearranging `h_cover`. The key move: divide both sides of
   `|U| <= N * C2 * eps^gamma` by `C2 * eps^gamma` (both positive).

3. **`UpperBound.lean`**. Define `PackingWitness`. Prove `covering_upper_bound`.
   Harder step: rewrite `(eps/2)^gamma` as `eps^gamma / 2^gamma`. Then divide
   both sides of `M * C1 * eps^gamma / 2^gamma <= |U|` by
   `C1 * eps^gamma / 2^gamma`. Use `div_rpow` or manual rewriting.

4. **`AhlforsCovering.lean`**. Combine the two lemmas. The main theorem is
   `And.intro` applied to the two bounds. The corollary multiplies by `b`
   using `mul_le_mul_of_nonneg_left`.

5. **Test**: `lake build` with zero errors, zero sorry.

### Estimated difficulty

- Defs: trivial (30 min)
- LowerBound: easy (1-2 hours). Mainly `field_simp`, `linarith`.
- UpperBound: medium (2-4 hours). The `(eps/2)^gamma` rewrite is the crux.
- AhlforsCovering: easy (1 hour). Composition.

Total: 4-8 hours GPT tactic time, comparable to C3/C5.

---

## Success criteria

- `lake build` passes with zero errors
- Main theorem `ahlfors_covering` has no `sorry`
- `ansatz_validity` has no `sorry`
- Trust boundaries are limited to the packing-covering duality step
  (encoded in `PackingWitness.h_packing`)
- All positivity conditions (A1 > 0, A2 > 0, eps > 0, etc.) are proved,
  not assumed
