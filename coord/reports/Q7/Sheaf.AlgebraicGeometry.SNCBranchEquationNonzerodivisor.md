## What changed

Proved `AlgebraicGeometry.sncBranchEquation_mul_injective` in
`Sheaf.AlgebraicGeometry.SNCBranchEquationNonzerodivisor`, with its signature unchanged.
A proved private helper shows that a global section whose zero locus lies in the support
of an invertible ideal acts injectively on global sections. On a Cartier chart with regular
generator g, the inclusion V(s) ⊆ V(g) implies g^n = c*s; cancellation of g^n proves that
s is regular. Sheaf separatedness combines the local cancellations. The branch-support
hypothesis supplies the required inclusion, the canonical affine global-sections
isomorphism transports cancellation to A, and closure of left-regular elements under finite
products proves the product assertion.

Updated the item's DAG proof, proof dependencies, proof origin, and Lean proof docstring
to this shorter argument. No statement, definition, public import, or consumer changed.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.sncBranchEquation_mul_injective`
(node `lem-sfb-snc-branch-equation-nonzerodivisor`). Proved the private helper
`mul_injective_of_zeroLocus_subset_support` in the same module. No holes added; zero
`sorry` remain in the delivery. No split-off statements.

The argument permits the zero ring and empty branch family: all cancellation and
nonzerodivisor lemmas allow subsingleton rings, and the empty product is 1. The helper
also allows an empty scheme, where local equality is vacuous and separatedness still
applies. It needs no reducedness or regularity assumption.

## No longer needed

Removed all seven former private proof imports:

- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Mathlib.RingTheory.Localization.AtPrime.Basic`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`
- `Mathlib.RingTheory.Spectrum.Maximal.Localization`
- `Mathlib.AlgebraicGeometry.StructureSheaf`

The proof no longer uses these old planned dependencies:
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-noetherian-ring`,
`def-weil-regular-scheme` (still a statement dependency), `lem-sc-regular-local-domain`,
`lem-weil-pbc-localization-at-prime-of-quotient`,
`lem-weil-pbc-noetherian-local-dimension-le-generators`,
`lem-weil-pbc-prime-localizations-jointly-injective`, and
`lem-weil-pbc-spec-domain-stalks-function-field`.
Their modules and declarations are retained in the library; this delivery removes only
this item's proof dependencies. All four public imports remain verbatim for consumers. The only private proof import
now needed is `Mathlib.Algebra.Regular.Pow`, for `IsLeftRegular.prod`.

The retained `def-trf-strict-normal-crossings-boundary` is used only through its
already-required effective Cartier clause; its approved tool use remains in the node.
The unit's own statement and realization route are preserved.

## Where the brief, the DAG or earlier work was wrong

The old dimension argument is unnecessary: the SNC definition already supplies an
invertible ideal for the whole boundary. The branch-support inclusion and elementary
radical criterion suffice, without matching reduced branch subschemes or their stalks.
The unchanged hypotheses about regularity of A, quotient reducedness, and distinctness
of branches are stronger than this proof needs; they remain in the public statement.
The new argument is agent-written from the effective Cartier clause of Stacks
`etale.tex`, `definition-strict-normal-crossings` (0BI9), the local description in
`divisors.tex`, `lemma-characterize-effective-Cartier-divisor`, and elementary algebra.

Validation: the complete module compiles without errors or warnings through
`lcompile.py` (7.5 seconds). `#print axioms` for the public theorem reports exactly
`propext`, `Classical.choice`, and `Quot.sound`. No new public declarations, consumer
adaptations, or definition changes.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
