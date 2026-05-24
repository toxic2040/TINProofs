# Blueprint C7: Support Failure via Rate-Distortion (Theorem 2, discussion v0.9 Section 15)

Source: `~/Desktop/TIN_daily/private_not_for_publication/discussion_v0.9.md`, lines 665-716
Also: `~/Desktop/Papers/theory/target_d_proof_and_regularity.md`, Part III

## Goal

Formalize the rate-distortion support failure theorem. Under the Markov
chain Y_U -> Z_dU -> Y_hat (interior -> boundary observable -> reconstruction),
the data processing inequality + capacity bound A4 force:

    R_U(eps) <= I(Y; Y_hat) <= I(Y; Z) <= C_b

Therefore: supportability at resolution eps requires R(eps) <= C_b.
Contrapositive: R(eps) > C_b implies no reconstruction at resolution eps.
Threshold: eps < eps* implies unsupportable.

This is information theory. The key ingredients are:
1. Data Processing Inequality (Markov chain -> MI is nonincreasing)
2. Channel capacity bound (A4: MI through boundary <= C_b)
3. Rate-distortion lower bound (achieving distortion eps requires MI >= R(eps))
4. Antitone R (finer resolution -> higher information demand)

All four are encoded as hypotheses in the scalar approach. The theorem is
the inequality chain and its consequences.

---

## Mathematical Statement

### Setup

- Y_U: interior state (random variable)
- Z_dU: boundary observable (carries all information between U and U^c)
- Y_hat: exterior reconstruction from Z_dU
- C_b = kappa * C(dU): boundary channel capacity (bits)
- d(Y, Y_hat) >= 0: distortion metric
- Resolution eps achieved if E[d(Y, Y_hat)] <= eps
- R_U(eps) := inf_{codes with E[d] <= eps} I(Y; Y_hat): rate-distortion function
- eps* := inf{eps > 0 : R(eps) <= C_b}: support threshold

### Key properties of R

- R is antitone (nonincreasing): finer resolution needs more information
- R is nonneg: mutual information is nonneg
- R(eps) = 0 for sufficiently large eps (trivial reconstruction)

### Theorem 2 (Support failure)

Supportability at resolution eps requires R(eps) <= C_b.

If eps < eps*, the description is unsupportable.

### Proof

The Markov chain Y -> Z -> Y_hat gives (DPI):

    I(Y; Y_hat) <= I(Y; Z)

By A4 (bounded flux across cuts):

    I(Y; Z) <= C_b

By definition of R (rate-distortion):

    R(eps) <= I(Y; Y_hat)

Chain: R(eps) <= I(Y; Y_hat) <= I(Y; Z) <= C_b.

Contrapositive: R(eps) > C_b -> no reconstruction achieves resolution eps.

For the threshold: if eps < eps* and a reconstruction with eps_eff <= eps existed,
then R(eps_eff) <= C_b. But R is antitone and eps_eff <= eps < eps*, so
R(eps_eff) >= R(eps) > C_b (by definition of eps*). Contradiction.

---

## Proof Structure (3 theorems)

### Theorem 1: Necessary condition for supportability

```
If a reconstruction at resolution eps exists (with I >= R(eps) and I <= C_b),
then R(eps) <= C_b.
```

Proof: R(eps) <= I <= C_b. Transitivity.

### Theorem 2: Support failure (contrapositive)

```
If R(eps) > C_b, then no reconstruction at resolution eps exists.
```

Proof: By contradiction. If a reconstruction exists, Theorem 1 gives
R(eps) <= C_b, contradicting R(eps) > C_b.

### Theorem 3: Below-threshold unsupportability

```
If eps < eps* and eps > 0, then no reconstruction at resolution eps exists.
```

Proof: eps < eps* implies R(eps) > C_b (threshold characterization).
Apply Theorem 2.

---

## Lean Formalization Strategy

### Key decision: scalar hypotheses (matching C3/C6 pattern)

The DPI, capacity bound, and rate-distortion lower bound are encoded as
hypotheses in witness structures. The mathematical content is the
inequality chain and its consequences (contradiction / threshold).

No measure-theoretic or information-theoretic infrastructure is built.
The scalar approach captures the mathematical argument faithfully.

### File structure

```
TINProofs/
├── C7/
│   ├── Defs.lean              -- SupportSetup, ReconstructionWitness, SupportThreshold
│   └── SupportFailure.lean    -- Three theorems: necessary, failure, threshold
```

Two files. The DPI and capacity are hypotheses in the witness structure,
not separate files.

### Type definitions

```lean
import Mathlib

noncomputable section

namespace TINProofs.C7

/-- Scalar data for the support failure theorem. -/
structure SupportSetup where
  C_b : ℝ
  R : ℝ → ℝ
  hC_b_pos : 0 < C_b
  hR_antitone : Antitone R
  hR_nonneg : ∀ ε, 0 ≤ R ε

/--
A reconstruction witness: an observer achieves resolution eps_eff
with mutual information I, subject to:
  - Rate-distortion lower bound: R(eps_eff) <= I
  - DPI + capacity upper bound: I <= C_b

These two hypotheses encode the entire chain
  R(eps) <= I(Y; Y_hat) <= I(Y; Z) <= C_b
in scalar form. The DPI step (I(Y;Y_hat) <= I(Y;Z)) and the capacity
step (I(Y;Z) <= C_b) are collapsed into the single hypothesis I <= C_b.
-/
structure ReconstructionWitness (S : SupportSetup) where
  I : ℝ
  eps_eff : ℝ
  heps_eff_pos : 0 < eps_eff
  hI_nonneg : 0 ≤ I
  h_rd_lower : S.R eps_eff ≤ I
  h_capacity : I ≤ S.C_b

/--
A support threshold: eps_star separates supportable (above) from
unsupportable (below) resolutions. Properties:
  - Above eps_star: R(eps) <= C_b (supportable in principle)
  - Below eps_star: R(eps) > C_b (unsupportable by Theorem 2)
-/
structure SupportThreshold (S : SupportSetup) where
  eps_star : ℝ
  heps_star_pos : 0 < eps_star
  h_above : ∀ ε, eps_star < ε → S.R ε ≤ S.C_b
  h_below : ∀ ε, 0 < ε → ε < eps_star → S.C_b < S.R ε

end TINProofs.C7

end
```

### Theorem sketches (SupportFailure.lean)

Four theorems, increasing in strength:

**1. support_necessary** (term proof, no tactic needed):
```lean
theorem support_necessary (S : SupportSetup)
    (w : ReconstructionWitness S) :
    S.R w.eps_eff ≤ S.C_b :=
  le_trans w.h_rd_lower w.h_capacity
```

**2. support_failure** (the core theorem, by contradiction):
```lean
theorem support_failure (S : SupportSetup) (ε : ℝ)
    (h_exceed : S.C_b < S.R ε) :
    ∀ (w : ReconstructionWitness S), ε < w.eps_eff := by
  sorry
```
Proof strategy: `intro w; by_contra h; push_neg at h` to get
`h : w.eps_eff ≤ ε`. Then:
  - `S.hR_antitone h` gives `S.R ε ≤ S.R w.eps_eff`
  - `w.h_rd_lower` gives `S.R w.eps_eff ≤ w.I`
  - `w.h_capacity` gives `w.I ≤ S.C_b`
  - Chain: `S.R ε ≤ S.C_b`. Use `linarith` against `h_exceed`.

**3. below_threshold_unsupportable** (combines threshold + failure):
```lean
theorem below_threshold_unsupportable (S : SupportSetup)
    (T : SupportThreshold S) (ε : ℝ)
    (hε_pos : 0 < ε) (hε_below : ε < T.eps_star) :
    ∀ (w : ReconstructionWitness S), ε < w.eps_eff := by
  sorry
```
Proof strategy: `exact support_failure S ε (T.h_below ε hε_pos hε_below)`.
One-liner applying h_below then support_failure.

**4. eps_star_le_eps_eff** (form needed by C8):
```lean
theorem eps_star_le_eps_eff (S : SupportSetup)
    (T : SupportThreshold S)
    (w : ReconstructionWitness S) :
    T.eps_star ≤ w.eps_eff := by
  sorry
```
Proof strategy: `by_contra h; push_neg at h` to get `h : w.eps_eff < T.eps_star`.
Then `below_threshold_unsupportable S T w.eps_eff w.heps_eff_pos h w` gives
`w.eps_eff < w.eps_eff`, contradicting `lt_irrefl`.

---

## Trust boundaries

1. **Data Processing Inequality**: encoded as the hypothesis h_capacity in
   ReconstructionWitness. The DPI says I(Y;Y_hat) <= I(Y;Z) for the Markov
   chain Y -> Z -> Y_hat. Combined with the capacity bound I(Y;Z) <= C_b,
   this gives I <= C_b. Not proved from first principles.

2. **Rate-distortion lower bound**: encoded as h_rd_lower. By definition of
   the rate-distortion function, any code achieving distortion eps has
   mutual information >= R(eps). This is Shannon's source coding converse.

3. **Antitone R**: encoded as hR_antitone. The rate-distortion function is
   nonincreasing because allowing more distortion can only reduce the
   required information rate. Standard in information theory.

4. **Threshold existence**: encoded in SupportThreshold. The existence of
   eps* with the stated separation property follows from R being antitone
   and the definition as an infimum. For right-continuous R, the infimum
   is achieved.

These are the same kind of honest boundaries as Kaas-Buhrman in C2 and
packing-covering duality in C6.

---

## Design choices

1. **ReconstructionWitness encodes the chain, not individual steps.**
   The DPI step and capacity step are collapsed into I <= C_b.
   Separating them would add a field for I(Y;Z) but no mathematical
   content. The scalar approach already loses the measure-theoretic
   structure; adding an intermediate scalar buys nothing.

2. **support_failure states eps < w.eps_eff, not nonexistence.**
   Rather than ¬∃ w, the theorem says: for any reconstruction w,
   the achieved resolution w.eps_eff is strictly above eps. This is
   a positive statement rather than a negation, and it's the form
   that C8 (Boundary Re-description) needs: any reconstruction has
   eps_eff >= eps*.

3. **SupportThreshold is a separate structure from SupportSetup.**
   The setup carries R and C_b. The threshold carries eps* and its
   characterization. This matches C6's separation of AhlforsSetup
   from CoveringWitness/PackingWitness.

4. **Namespace TINProofs.C7** (matches C1-C6 pattern).

---

## Connection to C8 (Boundary Re-description)

C8 needs two results from C7:

1. **Any reconstruction has eps_eff >= eps*.** This is exactly
   `below_threshold_unsupportable` — for any ε < eps*, any
   reconstruction w has ε < w.eps_eff.

2. **At eps*, the boundary summary Z* saturates the channel.**
   This is new content for C8: I(Y; Z*) = C_b and R(eps*) = C_b.
   It will be encoded as a hypothesis (trust boundary from
   rate-distortion achievability).

So C7's output feeds directly into C8's input.

---

## Mathlib modules to search

- `Mathlib.Order.Monotone.Basic` -- `Antitone`, `Monotone`
- `Mathlib.Order.Basic` -- `le_trans`, `lt_of_lt_of_le`, `not_le`
- `Mathlib.Tactic.Linarith` -- linear arithmetic
- `Mathlib.Tactic.Positivity` -- positivity proofs

The proofs are short inequality chains. The main tactic work is:
- `le_trans` for chaining
- `linarith` for linear arithmetic conclusions
- `Antitone` unfolding for monotonicity steps

---

## Known pitfalls

0. **Dot notation**: Use `supportSetup S` pattern not `S.supportSetup`
   for non-field defs, matching the C6 fix.

1. **Antitone direction**: `Antitone f` means `a ≤ b → f b ≤ f a`.
   So `eps_eff ≤ ε` gives `R ε ≤ R eps_eff`, NOT the reverse.
   The support_failure proof needs: if a reconstruction achieves
   eps_eff and eps_eff ≤ ε, then R(ε) ≤ R(eps_eff) ≤ I ≤ C_b.
   Wait — this gives R(ε) ≤ C_b, which CONTRADICTS R(ε) > C_b.
   But the theorem direction is: R(ε) > C_b → ε < eps_eff.
   The proof is by contradiction of ε ≥ eps_eff.

   Concretely: assume w.eps_eff ≤ ε. Then R(ε) ≤ R(w.eps_eff)
   (antitone) ≤ w.I (rd_lower) ≤ C_b (capacity). But R(ε) > C_b.
   Contradiction. So ε < w.eps_eff.

2. **Strict vs non-strict**: The threshold uses strict inequalities
   (eps < eps*) for unsupportability and strict inequality
   (eps* < eps) for supportability. At eps = eps*, behavior
   depends on continuity of R and is left unspecified.

3. **The lt_of_le_of_lt / lt_irrefl pattern**: The contradiction
   in support_failure goes: R(ε) ≤ C_b (derived) contradicts
   C_b < R(ε) (hypothesis). Use `linarith` or `exact absurd h1 (not_le.mpr h2)`.

---

## GPT workflow

1. **`Defs.lean` is already done.** Zero sorry. Just structures.

2. **`SupportFailure.lean`**. Four theorems, all short:

   a. `support_necessary`: already done as a term proof (no sorry).

   b. `support_failure`: the core theorem. By contradiction.
      Key steps: `intro w`, `by_contra h`, `push_neg at h` to get
      `h : w.eps_eff ≤ ε`. Then chain:
        `have h1 := S.hR_antitone h`   -- R(ε) ≤ R(eps_eff)
        `have h2 := w.h_rd_lower`       -- R(eps_eff) ≤ I
        `have h3 := w.h_capacity`        -- I ≤ C_b
        `linarith`                       -- contradicts h_exceed : C_b < R(ε)

   c. `below_threshold_unsupportable`: one-liner.
      `exact support_failure S ε (T.h_below ε hε_pos hε_below)`

   d. `eps_star_le_eps_eff`: by contradiction.
      `by_contra h; push_neg at h` to get `h : w.eps_eff < T.eps_star`.
      Then `have := below_threshold_unsupportable S T w.eps_eff w.heps_eff_pos h w`
      gives `w.eps_eff < w.eps_eff`. Use `exact absurd this (lt_irrefl _)`
      or `linarith`.

3. **Test**: `lake build` with zero errors, zero sorry.

### Estimated difficulty

- Defs: done (0 min)
- SupportFailure: easy (30 min - 1 hour). All proofs are short inequality chains.

Total: under 1 hour GPT tactic time. Shortest of the series so far.

---

## Wiring into the project

After all sorry are filled, add to `TINProofs.lean`:
```lean
import TINProofs.C7.Defs
import TINProofs.C7.SupportFailure
```

And add to `TINProofs/Statements.lean`:
```lean
import TINProofs.C7.SupportFailure

-- ===================================================================
-- C7. Support Failure via Rate-Distortion  (Theorem 2)
-- ===================================================================

/- **Paper.** Under the Markov chain Y -> Z -> Y_hat and capacity
    bound I(Y;Z) <= C_b, achieving resolution eps requires
    R(eps) <= C_b. Below the threshold eps*, no reconstruction
    achieves resolution eps.

    **Lean.** `support_necessary`, `support_failure`,
    `below_threshold_unsupportable`, `eps_star_le_eps_eff`. -/
#check @TINProofs.C7.support_necessary
#check @TINProofs.C7.support_failure
#check @TINProofs.C7.below_threshold_unsupportable
#check @TINProofs.C7.eps_star_le_eps_eff
```

## Success criteria

- `lake build` passes with zero errors
- All four theorems have no `sorry`
- Trust boundaries limited to: DPI (h_capacity), rate-distortion
  lower bound (h_rd_lower), R antitone (hR_antitone), threshold
  existence (SupportThreshold hypotheses)
