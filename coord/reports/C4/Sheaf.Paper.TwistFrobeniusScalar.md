## What changed

Proved `WeilConjectures.TwistFrobeniusScalar.signedQuotients_existsUnique`.
A proved private helper, for an arbitrary scheme, constructs the normalized
quotient isomorphism on every nonnegative tensor power from `signedTwistFirstReduction` and the existing
`positiveComparison` construction. Its quotient family satisfies the three
`IsAdicPurityRootQuotients` clauses, so uniqueness identifies it with the published
family. Negative quotient maps extend functionals by `scalarDualBaseMap` and
precompose with the inverse positive comparison. Their evaluation formula is
proved directly. Uniqueness is proved on every slice by scalar-extension tensor
generation and naturality, reducing to the prescribed identity-slice equations.
All public signatures and definition bodies are unchanged.
The parent node and theorem docstring record the construction and its actual
dependencies. The proof establishes the generic scheme assertion explicitly and
then specializes it to the geometric point. This keeps the fibre construction out
of repeated instance and definitional-equality checks. The two new proofs elaborate
synchronously inside a local section; the surrounding declarations retain their
original settings. Repeated sheafification and slice-local
bijectivity instances are cached and intentionally inlined in the two proof
contexts. The local `haveILetI` style exception preserves this normalization
behavior; all surrounding linter settings are unchanged.

The new imports are proof-only: `SignedTwistFirstReduction`, the private positive
comparison API of `SignedLineScalarTensorTower`, and the hidden defining equation
of `adicPurityRootQuotients` from `AdicPurityRootComparisons`. The last module's
existing public import is retained for the existing interface.

## Proved and sorry left

Closed 1 of the 5 original holes:
`WeilConjectures.TwistFrobeniusScalar.signedQuotients_existsUnique`
(`lem-pur-twist-frobenius-scalar`). Added 0 holes; split off 0 statements.
The proof uses the existing admitted uniqueness theorem
`WeilConjectures.adicPurityRootQuotients_existsUnique`.

The four untouched holes are:

- `WeilConjectures.TwistFrobeniusScalar.reductionSheafLine_existsUnique`
  (`lem-pur-twist-frobenius-scalar`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_finite_integral`
  (`lem-pur-twist-frobenius-scalar-finite-integral`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_rational_qbar`
  (`lem-pur-twist-frobenius-scalar-rational-qbar`).
- `WeilConjectures.TwistFrobeniusScalar.twist_frobenius_scalar_reduction_localization`
  (`lem-pur-twist-frobenius-scalar-reduction-localization`).

## No longer needed

No existing imports or modules are removed. The signed quotient helper needs no
primitive-root coordinates, rank-one trivialization, point-section exactness,
Frobenius transport, or flatness of the coefficient quotient. Those dependencies
remain relevant to the other admitted components, so no global pruning is claimed.
The conventions unit has no realized statement or proof steps; its route is unchanged.

The added dependencies are used as general coefficient tools: normalized first-line
quotient, ordinary tensor powers, and scalar extension of internal functionals.
They do not replace a step of another blueprint unit. In particular the proof uses
only the characteristic-independent positive construction inside the signed-line
module, without invoking its rank-one hypotheses or signed comparison theorem.
The node also cites `lem-sp-scalar-extension-binary-coherence`: its unit and binary
isomorphisms supply the elementary induction on nonnegative powers implemented by
the proved private construction. No local-basis assertion is taken from the
stronger signed-line statement.

## Where the brief, the DAG or earlier work was wrong

The existing caution about the missing `l ≠ D.p` parameter is relevant to applying
`signedTwistReduction_comparison`, but does not prevent proving the signed quotient
helper with its full signature. Nonnegative ordinary scalar extension needs no
local-freeness assumption, and a functional extends across an ordinary tensor
quotient once the positive comparison is invertible. The negative quotient maps
need not themselves be isomorphisms here. This proves the stated helper without
adding a hypothesis, including `l = D.p`, exponent zero, every negative exponent,
and the first positive quotient level `n = 0`.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
