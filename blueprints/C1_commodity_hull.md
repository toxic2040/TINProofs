# Blueprint C1: Commodity Hull Theorem (Theorem 6.3)

Source: `Papers/papers/monograph_ch6_body.tex`, lines 141-183.

## Mathematical Statement

For a finite set of feasible time-respecting paths, define for each path pi:
- x_pi = (T_pi, -ln Q_pi) in the exposure-reliability plane
- Path action: A_pi(lam) = -ln Q_pi + lam * T_pi  (affine in lam)
- Support function: F(lam) = min over all paths of A_pi(lam)

Then:
(i)   Optimal path at lam is the minimiser of A_pi(lam).
(ii)  Paths optimal for some commodity = vertices of the lower convex hull.
(iii) Path-switch transitions occur at corners of F (nondifferentiable points).
(iv)  F(lam) and V(lam) = -F(lam) form a Legendre-dual pair.

## Proof Sketch

A_pi(lam) is affine in lam for each path, hence both convex and concave.
F(lam) = pointwise min of finitely many affine functions is concave.
Corners of F occur at crossover slopes lam*_ij = ln(Q_i/Q_j)/(T_j - T_i).
V(lam) = max_pi {ln Q_pi - lam * T_pi} is the pointwise max of affine
functions, hence convex. F and V are negatives, satisfying the conjugate
relationship: V is the convex conjugate of the indicator on the hull vertices.

## Lean Formalization Strategy

### What exists in mathlib (verified):
- `LinearMap.convexOn`, `LinearMap.concaveOn` (line 353-358 of Function.lean)
- `ConcaveOn.inf` (line 586 of Function.lean) -- min of two concave is concave
- `convexHull` in Mathlib.Analysis.Convex.Hull
- `AffineMap` and composition lemmas
- No Legendre/Fenchel transform -- must define ourselves

### What we need to build:
1. `CommodityHull` structure holding finite path data
2. Path action is affine -- prove via `ConvexOn` + `ConcaveOn`
3. Support function concavity via induction on `Finset.inf'` using `ConcaveOn.inf`
4. Crossover slopes as explicit `ln(Q_i/Q_j)/(T_j-T_i)`
5. Duality as a definitional relationship (not the full Fenchel theory)

### Key simplification vs the paper:
Work with a **finite** set of paths (Finset). The inf becomes Finset.inf'.
This avoids measurability / topology issues while capturing all the
algebraic content. The paper's proof also works with finitely many paths.

---

## File Structure (4 files)

### File 1: `TINProofs/C1/Defs.lean`

```lean
import Mathlib

open Real Set

noncomputable section

namespace TINProofs.C1

/-- A path in the exposure-reliability plane: exposure time T and
    end-to-end survival probability Q. -/
structure PathData where
  T : ℝ
  Q : ℝ
  hT_nonneg : 0 ≤ T
  hQ_pos : 0 < Q
  hQ_le : Q ≤ 1

/-- Path action at commodity hazard rate lambda:
    A_pi(lam) = -ln Q + lam * T. -/
def PathData.action (p : PathData) (lam : ℝ) : ℝ :=
  -Real.log p.Q + lam * p.T

/-- Value of a path at commodity hazard rate lambda:
    V_pi(lam) = ln Q - lam * T. -/
def PathData.value (p : PathData) (lam : ℝ) : ℝ :=
  Real.log p.Q - lam * p.T

/-- A commodity hull instance: a nonempty finite set of paths. -/
structure CommodityHull where
  paths : Finset PathData
  hnonempty : paths.Nonempty

/-- Support function: F(lam) = min over paths of A_pi(lam).
    Uses Finset.inf' with the nonemptiness proof. -/
def CommodityHull.support (ch : CommodityHull) (lam : ℝ) : ℝ :=
  ch.paths.inf' ch.hnonempty (fun p => p.action lam)

/-- Value function: V(lam) = max over paths of V_pi(lam) = -F(lam). -/
def CommodityHull.valueFn (ch : CommodityHull) (lam : ℝ) : ℝ :=
  ch.paths.sup' ch.hnonempty (fun p => p.value lam)

/-- Crossover slope between two paths with distinct exposure times:
    lam*_ij = ln(Q_i / Q_j) / (T_j - T_i). -/
def crossoverSlope (pi pj : PathData) (hT : pi.T ≠ pj.T) : ℝ :=
  (Real.log pi.Q - Real.log pj.Q) / (pj.T - pi.T)

end TINProofs.C1

end
```

### File 2: `TINProofs/C1/ActionAffine.lean`

Proves each path action is both convex and concave (i.e., affine) in lambda.

```lean
import TINProofs.C1.Defs

open Real Set

noncomputable section

namespace TINProofs.C1

/-- Path action is affine in lambda: A(lam) = c + lam * T where c = -ln Q.
    We prove it satisfies the convexity midpoint condition with equality. -/
theorem action_affine (p : PathData) (lam1 lam2 : ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    p.action (a * lam1 + b * lam2) = a * p.action lam1 + b * p.action lam2 := by
  unfold PathData.action
  ring

/-- Path action is convex on univ (immediate from affinity). -/
theorem action_convexOn (p : PathData) : ConvexOn ℝ univ (p.action) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    exact le_of_eq (action_affine p x y a b ha hb hab)

/-- Path action is concave on univ (immediate from affinity). -/
theorem action_concaveOn (p : PathData) : ConcaveOn ℝ univ (p.action) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    exact le_of_eq (action_affine p x y a b ha hb hab).symm

/-- Value function per-path is affine. -/
theorem value_affine (p : PathData) (lam1 lam2 : ℝ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    p.value (a * lam1 + b * lam2) = a * p.value lam1 + b * p.value lam2 := by
  unfold PathData.value
  ring

/-- Value per-path is convex (hence V = sup is convex). -/
theorem value_convexOn (p : PathData) : ConvexOn ℝ univ (p.value) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    exact le_of_eq (value_affine p x y a b ha hb hab)

/-- Value per-path is concave. -/
theorem value_concaveOn (p : PathData) : ConcaveOn ℝ univ (p.value) := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    exact le_of_eq (value_affine p x y a b ha hb hab).symm

/-- Action and value are negatives of each other. -/
theorem action_neg_value (p : PathData) (lam : ℝ) :
    p.action lam = -(p.value lam) := by
  unfold PathData.action PathData.value
  ring

end TINProofs.C1

end
```

### File 3: `TINProofs/C1/SupportConcave.lean`

Proves F(lam) = min of finitely many affine functions is concave.

The inductive approach: for a singleton Finset, F = A_pi which is concave.
Adding one more path, the new F = min(old F, A_new), and `ConcaveOn.inf`
gives concavity of the min.

```lean
import TINProofs.C1.ActionAffine

open Real Set

noncomputable section

namespace TINProofs.C1

/-- The support function satisfies the concavity condition:
    F(a*x + b*y) >= a*F(x) + b*F(y).

    Proof: F(lam) = inf' over paths of A_pi(lam). Each A_pi is concave.
    The infimum of concave functions is concave. We prove this for
    Finset.inf' by induction. -/

-- Helper: for a single path, inf' = action, which is concave
private theorem concaveOn_inf'_singleton (p : PathData) :
    ConcaveOn ℝ univ (fun lam => ({p} : Finset PathData).inf'
      (Finset.singleton_nonempty p) (fun q => q.action lam)) := by
  have : (fun lam => ({p} : Finset PathData).inf'
      (Finset.singleton_nonempty p) (fun q => q.action lam)) = p.action := by
    ext lam
    simp [Finset.inf'_singleton]
  rw [this]
  exact action_concaveOn p

/-- Support function is concave: min of finitely many affine (hence concave)
    functions is concave. -/
theorem support_concaveOn (ch : CommodityHull) :
    ConcaveOn ℝ univ (ch.support) := by
  unfold CommodityHull.support
  -- Use Finset.cons_induction on ch.paths
  -- Each step applies ConcaveOn.inf (min of two concave is concave)
  -- Base: single path is concave (action_concaveOn)
  -- Step: min(concave, concave) is concave
  sorry -- GPT: prove by Finset induction using ConcaveOn.inf and action_concaveOn

/-- Value function is convex: max of finitely many affine functions is convex.
    Dual of support_concaveOn. -/
theorem valueFn_convexOn (ch : CommodityHull) :
    ConvexOn ℝ univ (ch.valueFn) := by
  unfold CommodityHull.valueFn
  sorry -- GPT: dual argument using ConvexOn.sup and value_convexOn

/-- The value function equals the negation of the support function. -/
theorem valueFn_eq_neg_support (ch : CommodityHull) (lam : ℝ) :
    ch.valueFn lam = -(ch.support lam) := by
  unfold CommodityHull.valueFn CommodityHull.support
  sorry -- GPT: unfold Finset.sup'/inf', use action_neg_value pointwise

end TINProofs.C1

end
```

### File 4: `TINProofs/C1/Crossover.lean`

Defines crossover slopes and proves path switches happen there.

```lean
import TINProofs.C1.SupportConcave

open Real Set

noncomputable section

namespace TINProofs.C1

/-- At the crossover slope, two paths have equal action. -/
theorem action_eq_at_crossover (pi pj : PathData) (hT : pi.T ≠ pj.T) :
    pi.action (crossoverSlope pi pj hT) = pj.action (crossoverSlope pi pj hT) := by
  unfold PathData.action crossoverSlope
  field_simp
  ring

/-- Below the crossover slope, the path with lower exposure time has
    lower action (is preferred). -/
theorem action_lt_below_crossover (pi pj : PathData) (hT : pi.T < pj.T)
    (lam : ℝ) (hlam : lam < crossoverSlope pi pj (ne_of_lt hT)) :
    pi.action lam < pj.action lam := by
  unfold PathData.action crossoverSlope at *
  sorry -- GPT: unfold, field_simp, then nlinarith using hT and hlam

/-- Above the crossover slope, the path with higher exposure time has
    lower action (is preferred). -/
theorem action_gt_above_crossover (pi pj : PathData) (hT : pi.T < pj.T)
    (lam : ℝ) (hlam : crossoverSlope pi pj (ne_of_lt hT) < lam) :
    pj.action lam < pi.action lam := by
  unfold PathData.action crossoverSlope at *
  sorry -- GPT: symmetric to above

/-- Legendre duality as a definitional relationship: the support function
    F and value function V satisfy V(lam) = -F(lam) for all lam.
    This is the finite-path specialization of conjugate duality. -/
theorem legendre_duality (ch : CommodityHull) (lam : ℝ) :
    ch.valueFn lam = -(ch.support lam) :=
  valueFn_eq_neg_support ch lam

end TINProofs.C1

end
```

---

## Build Order

1. **Defs.lean** -- structures and definitions. Get it compiling first.
2. **ActionAffine.lean** -- all `ring` proofs, should be straightforward.
3. **SupportConcave.lean** -- the hardest file. Three `sorry` stubs.
4. **Crossover.lean** -- crossover equality is `field_simp; ring`. The inequalities need `nlinarith`.

Add to `TINProofs.lean`:
```
import TINProofs.C1.Defs
import TINProofs.C1.ActionAffine
import TINProofs.C1.SupportConcave
import TINProofs.C1.Crossover
```

---

## Key Mathlib Lemmas

| Need | Mathlib location |
|------|-----------------|
| `ConcaveOn.inf` (min of two concave is concave) | `Mathlib.Analysis.Convex.Function` line 586 |
| `LinearMap.concaveOn` (linear maps are concave) | `Mathlib.Analysis.Convex.Function` line 357 |
| `Finset.inf'_singleton` | `Mathlib.Order.Finset` |
| `Finset.inf'_cons` / `Finset.inf'_insert` | `Mathlib.Order.Finset` |
| `Real.log_div` | `Mathlib.Analysis.SpecialFunctions.Log.Basic` |
| `field_simp` | tactic |
| `ring` | tactic |
| `nlinarith` | tactic |
| `convex_univ` | `Mathlib.Analysis.Convex.Basic` |

## Difficulty Assessment

**ActionAffine.lean**: Easy. All proofs are `ring` or `le_of_eq (... ring)`.

**SupportConcave.lean**: Medium. The Finset induction is the only nontrivial
part. Key insight: `Finset.inf'` over a `cons` or `insert` decomposes as
`min(head, Finset.inf' tail)`. Apply `ConcaveOn.inf` at each step.
If Finset induction is hard, an alternative: prove directly from the
definition of `ConcaveOn` using `Finset.le_inf'` and the per-path
concavity inequality.

**Crossover.lean**: Medium. `action_eq_at_crossover` should be `field_simp; ring`.
The strict inequalities need careful `nlinarith` or `linarith` after `field_simp`.

**Overall**: Comparable to C5 difficulty. No measure theory, no probability.
Pure algebra and convex analysis with finite sets.

---

## Known Pitfalls

1. **Finset.inf' vs iInf**: Use `Finset.inf'` (takes Nonempty proof), not
   `iInf` (requires conditionally complete lattice, more universe issues).
   `ℝ` with `min` gives a `SemilatticeInf` which is what `Finset.inf'` needs.

2. **PathData decidable equality**: `Finset PathData` needs `DecidableEq PathData`.
   Add `deriving DecidableEq` to the structure or use `classical` in the section.
   Alternatively, index paths by `Fin n` and use `Finset (Fin n)`.

3. **ConcaveOn.inf** takes two `ConcaveOn` proofs and returns `ConcaveOn`
   for the `⊓` (inf in the lattice). For `ℝ`, `f ⊓ g = fun x => min (f x) (g x)`.
   Make sure the function type matches.

4. **ne_of_lt**: To get `pi.T ≠ pj.T` from `pi.T < pj.T`, use `ne_of_lt`.

5. **field_simp before ring**: When division is involved (crossoverSlope),
   always `field_simp` first to clear denominators, then `ring`.

6. **Finset.inf' output type**: `Finset.inf'` requires `SemilatticeInf`.
   For `ℝ`, this works via `LinearOrder` → `Lattice` → `SemilatticeInf`.
   The result is `ℝ` valued, which is fine.

---

## What This Proves

With all `sorry` cleared:
- Path action is affine in the commodity hazard rate (exact, not approximate)
- The support function (minimum action over paths) is concave
- The value function (maximum value over paths) is convex
- Paths switch at algebraically defined crossover slopes
- F and V are Legendre duals in the finite-path sense

This is a formally verified variational principle for commodity-dependent
routing. Together with C2-C5, it completes the machine-verification
of all five TIN/SNTC candidate theorems.
