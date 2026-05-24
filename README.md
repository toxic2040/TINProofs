# TINProofs

Machine-verified Lean 4 proofs for five theorems from the TIN/SNTC delay-tolerant
networking papers.

## Proof Blocks

| Block | Theorem | Domain |
|-------|---------|--------|
| C1 | Commodity Hull (Thm 6.3) | Convex analysis, Legendre duality |
| C2 | Stochastic Certification Asymmetry (Thm S2) | Binomial/Poisson probability |
| C3 | Lyapunov Radius of Validity (Prop C1) | Dynamical systems |
| C4 | Temporal Transport Factorization (Lem 2.6) | Measure-theoretic probability |
| C5 | Three-Factor Sparse Law (Prop 2.7) | Algebraic decomposition |

26 modules, 1404 source lines, 124 top-level declarations, 76 theorem or lemma
declarations. Zero `sorry`.

## Trust Boundaries

Two external results are stated as named hypotheses rather than proved from
first principles:

- **Binomial median upper bound** (Kaas & Buhrman 1980) -- used in C2
  absorbing-tier cutoff.
- **Poisson median asymptotic** (Adell & Jodra 2005) -- used in C2 delivery-ratio
  expansion.

C3 abstracts the Lyapunov setup into scalar inequalities; the connection to the
paper's matrix/Taylor hypotheses is an explicit review boundary.

## Build

Requires [elan](https://github.com/leanprover/elan) with Lean 4.29.1.

```
source ~/.elan/env
cd TINProofs          # or wherever you cloned this
lake build
```

First build fetches mathlib v4.29.1 and takes several minutes. Subsequent
incremental builds are fast.

## Documentation

- `output/pdf/TINProofs_C1_C5_formal_lemmas.pdf` -- theorem statements in
  traditional mathematical notation.
- `output/pdf/TINProofs_C1_C5_peer_review_packet.pdf` -- full declaration list
  with review notes for each block.
- `blueprints/` -- design documents used during development.

## License

MIT. See [LICENSE](LICENSE).
