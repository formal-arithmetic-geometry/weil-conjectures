## What changed

Completed `AlgebraicGeometry.Etale.rawChartScalarCounitPasting` in
`Sheaf.Paper.RawChartScalarCounitPasting`, with all public signatures and definitions
unchanged. Added three proved private helpers: `rawChartScalarIso_factor`,
`chartProperty_of_iso`, and `rawChart_domains`.

The right factorization follows directly from the published definition of
`reductionEtaleChartScalarIso` and naturality of the exact/left-derived pullback
comparison. Domains follow from `etaleCtfChartDomain`, the existing ordered affine
right normal form, and normalization of compact support to sum extension.
The composite equation uses naturality of the actual sum counit, the existing
`etaleSumCounitScalar` equation, naturality of `etaleCoefficientMap`, and the existing
`affine_counit_scalar` equation. The unit's sum-then-ordered-affine route is preserved.

Added private proof imports for `AffineTraceRightNormalForm`,
`ConstructibleEtaleModuleSheafComparison`, and `EtaleDerivedTensorSymmetry`.
Updated the item's proof steps and proof dependencies to this argument.
Validation: the complete module compiled through lcompile.py in 27.2 seconds,
with exit code 0 and no warnings. Public-definition text and the theorem signature
were compared with the current source and are unchanged.
The existing node `lem-amb-affine-trace-right-normal-form` is used as a tool for its
natural isomorphism of the ordered right functor with twisted shifted pullback.
The existing `lem-sp-et-proet-coefficient-compatibility` supplies its proved
naturality theorem. No new maintainer tool approvals were written.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.rawChartScalarCounitPasting`
(node `lem-sp-raw-chart-scalar-counit-pasting`).
Added zero holes. Zero textual `sorry` remain in the delivery's Lean module.
The stated dependency theorems are used as authorized by stage 3; this does not
claim that their transitive proofs are already free of holes.

## No longer needed

Removed these unused private proof imports and corresponding direct proof dependencies:

- `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`
  (`lem-sfb-ringed-derived-monoidal-comparisons`).
- `Sheaf.Paper.FiniteTateBalancedScalarPullback`
  (`lem-sp-finite-tate-balanced-scalar-pullback`).
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
  (`lem-asd-etale-finite-twist-pullback`).
- `Sheaf.Paper.CochainPullbackTensorShift`
  (`lem-weil-pbc-cochain-pullback-tensor-shift`).

The published chart comparison already specifies the ordered composite, so its
factorization needs none of those separate coherence theorems. Removed the obsolete
top-level `tool_uses` approvals for monoidal comparisons, finite twist pullback, and
cochain pullback/tensor/shift. Finite twist pullback remains needed transitively by
the existing normal-form theorem; these are local dependency prunings, not requests
to withdraw any module or declaration. All public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG's Step 2 planned a fresh calculation on K-flat models. The published
`reductionEtaleChartScalarIso` definition already factors the canonical comparison;
only naturality of its presentation isomorphism is needed here.
Step 1 needs the actual bridge from the ordered affine right model to the chart
operation: `affineTraceRight_normalForm` supplies it. Tensor symmetry converts its
right tensor convention to the domain theorem's left tensor convention.

Checked dimension zero, zero input, empty schemes, and n=0 (hence zero coefficient
rings) against the argument: no cancellation of nonzero data or positive dimension
is used. The only positivity is ell^n > 0, which holds also for n=0.
No target or dependency statement was changed; no new nodes or change records.

## Second reading by P6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
