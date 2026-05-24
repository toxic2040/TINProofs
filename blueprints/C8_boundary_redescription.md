# Blueprint C8: Boundary Re-description Theorem (Theorem 3, discussion v0.9 Section 16)

Source: `~/Desktop/TIN_daily/private_not_for_publication/discussion_v0.9.md`, lines 720-757
Also: `~/Desktop/Papers/theory/target_d_proof_and_regularity.md`, Part IV

## Goal

Formalize the boundary re-description theorem — the crown jewel of the
substrate program's proved content.

Support failure does not produce inconsistency. It forces the description
of a region's interior to factor through an optimal boundary summary at
exactly the threshold resolution. Sub-threshold details are causally
disconnected from the exterior.

This is the mathematical skeleton of holographic boundary encoding,
proved from rate-distortion theory. The first machine-verified proof
of this result.

---

## Mathematical Statement

### Theorem 3 (Boundary re-description)

Given the C7 setup (boundary capacity C_b, rate-distortion function R,
threshold eps_star):

**Part 1 (Resolution floor):** For any exterior reconstruction Y_hat,
the achieved resolution eps_eff satisfies:

    eps_eff >= eps_star

**Part 2 (Optimal boundary summary):** There exists a boundary summary
Z* that:
  - Saturates the channel: I(Y; Z*) = C_b
  - Achieves exactly the threshold: R(eps_star) = C_b
  - Is the optimal lossy compression at the threshold resolution

**Part 3 (Consequences):**
  1. Channel saturation: Z* uses all available boundary capacity
  2. Sufficiency: Z* is the optimal description at eps_star
  3. Causal disconnection: for eps < eps_star, R(eps) > C_b,
     meaning sub-threshold details cannot pass the boundary

### Proof

**Part 1:** From C7.eps_star_le_eps_eff. Already proved.

**Part 2:** Let Z* saturate the cut: I(Y; Z*) = C_b. By
rate-distortion theory, Z* achieves the distortion eps such that
R(eps) = C_b. By definition of eps_star, this eps = eps_star.
(This is a trust boundary — Shannon's source coding achievability.)

**Part 3:** For any reconstruction at eps_eff = eps_star:
R(eps_star) = C_b <= I_recon (by R being the infimum).
For eps < eps_star: C_b < R(eps) (threshold characterization).
The deficit R(eps) - C_b > 0 quantifies inaccessible information.

---

## Proof Structure (7 theorems)

### resolution_floor (already proved, term proof)

```
T.eps_star <= r.eps_eff
```
Direct application of C7.eps_star_le_eps_eff via the toWitness coercion.

### boundary_summary_achieves_threshold

```
S.R T.eps_star <= S.C_b
```
From BoundarySummary.h_rd_at_threshold: R(eps_star) = C_b, so
R(eps_star) <= C_b trivially.

### boundary_summary_saturates (already proved, term proof)

```
Z.I_star = S.C_b
```
Direct from Z.h_saturates.

### rate_equals_capacity_at_threshold (already proved, term proof)

```
S.R T.eps_star = S.C_b
```
Direct from Z.h_rd_at_threshold.

### boundary_summary_optimal

```
Given r with r.eps_eff = T.eps_star: S.C_b <= r.I_recon
```
Chain: C_b = R(eps_star) <= I_recon.
Uses Z.h_rd_at_threshold to get R(eps_star) = C_b,
then r.h_rd to get R(eps_eff) <= I_recon,
then h_achieves to substitute eps_eff = eps_star.

### information_deficit_pos

```
0 < S.R ε - S.C_b
```
From T.h_below: C_b < R(eps). Rearrange to R(eps) - C_b > 0.

### boundary_redescription (combined theorem)

```
(∀ r, T.eps_star ≤ r.eps_eff) ∧
S.R T.eps_star = S.C_b ∧
(∀ ε, 0 < ε → ε < T.eps_star → S.C_b < S.R ε)
```
Conjunction of resolution_floor, rate_equals_capacity_at_threshold,
and subthreshold_inaccessible.

---

## Lean Formalization Strategy

### Key decision: build on C7, minimal new infrastructure

C8 imports C7.SupportFailure and reuses SupportSetup, SupportThreshold,
and ReconstructionWitness. The only new structures are:

- BoundarySummary: carries the trust boundary (Z* exists and saturates)
- ExteriorReconstruction: thin wrapper around ReconstructionWitness
  with a toWitness coercion

### File structure

```
TINProofs/
├── C8/
│   ├── Defs.lean                  -- BoundarySummary, ExteriorReconstruction
│   └── BoundaryRedescription.lean -- All 7 theorems
```

### Trust boundaries

1. **BoundarySummary existence**: The claim that Z* exists with
   I(Y;Z*) = C_b and R(eps_star) = C_b is Shannon's source coding
   achievability theorem (forward direction). Encoded as hypotheses
   h_saturates and h_rd_at_threshold in the BoundarySummary structure.

2. **Everything from C7**: DPI (h_capacity), rate-distortion lower
   bound (h_rd_lower), R antitone (hR_antitone), threshold existence
   (SupportThreshold). These carry through unchanged.

---

## GPT workflow

1. **`Defs.lean` is done.** Zero sorry. BoundarySummary and
   ExteriorReconstruction compile clean, including the toWitness coercion.

2. **`BoundaryRedescription.lean`**. Seven theorems, four with sorry:

   a. `resolution_floor`: already proved (term proof using C7).

   b. `boundary_summary_achieves_threshold`: from Z.h_rd_at_threshold.
      R(eps_star) = C_b implies R(eps_star) <= C_b.
      Tactic: `rw [Z.h_rd_at_threshold]` or `exact le_of_eq Z.h_rd_at_threshold`.

   c. `boundary_summary_saturates`: already proved (term proof).

   d. `rate_equals_capacity_at_threshold`: already proved (term proof).

   e. `boundary_summary_optimal`: the key new proof.
      Given h_achieves : r.eps_eff = T.eps_star:
        `have h1 : S.R T.eps_star = S.C_b := Z.h_rd_at_threshold`
        `have h2 : S.R r.eps_eff ≤ r.I_recon := r.h_rd`
        `rw [h_achieves] at h2`
        `linarith`
      Chain: C_b = R(eps_star) <= I_recon.

   f. `information_deficit_pos`: from T.h_below.
      `have h := T.h_below ε hε_pos hε_below`  -- C_b < R(eps)
      `linarith`

   g. `boundary_redescription`: conjunction of previous results.
      `exact ⟨fun r => resolution_floor S T r,
              Z.h_rd_at_threshold,
              fun ε hε_pos hε_below => T.h_below ε hε_pos hε_below⟩`
      Or use `refine ⟨?_, ?_, ?_⟩` and fill each branch.

3. **Test**: `lake build` with zero errors, zero sorry.

---

## Wiring into the project

After all sorry are filled, add to `TINProofs.lean`:
```lean
import TINProofs.C8.Defs
import TINProofs.C8.BoundaryRedescription
```

And add to `TINProofs/Statements.lean`:
```lean
import TINProofs.C8.BoundaryRedescription

-- ===================================================================
-- C8. Boundary Re-description  (Theorem 3)
-- ===================================================================

/- **Paper.** Support failure forces the interior description to
    factor through an optimal boundary summary Z* at the threshold
    resolution eps_star. Any exterior reconstruction has eps_eff >= eps_star.
    At the threshold, R(eps_star) = C_b (channel saturated).
    Below the threshold, R(eps) > C_b (causally disconnected).

    **Lean.** `resolution_floor`, `boundary_summary_optimal`,
    `boundary_redescription`. -/
#check @TINProofs.C8.resolution_floor
#check @TINProofs.C8.boundary_summary_optimal
#check @TINProofs.C8.boundary_redescription
```

---

## Connection to the substrate program

This theorem is the mathematical skeleton of holographic boundary encoding.
It says:

1. No observer outside a region can resolve its interior below eps_star.
2. The optimal exterior description is a boundary summary using exactly
   the available channel capacity.
3. Sub-threshold interior details are information-theoretically
   inaccessible from outside.

The physical conjecture (discussion v0.9 §43 item 3) is that this
substrate-side Z* corresponds to gravitational horizons. That
identification remains open and is NOT part of C8. C8 proves the
information-theoretic mechanism; the physical interpretation is
future work.

Formalizing this in Lean is unprecedented. No existing formal
verification library contains a machine-verified proof of the
rate-distortion mechanism behind boundary-summary sufficiency.

---

## Success criteria

- `lake build` passes with zero errors
- All seven theorems have no `sorry`
- Trust boundaries limited to: BoundarySummary existence
  (h_saturates, h_rd_at_threshold) plus everything inherited from C7
- The combined theorem `boundary_redescription` states the full
  three-part result as a single declaration
