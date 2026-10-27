## What changed

Completed `AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison_isIso`
in `Sheaf.Paper.FreeParameterScalarMaps`. The proof obtains the existing universally
normalized scalar/geometric comparison from
`QuotientChange.internal_pull_normalization_exists`, identifies its inverse using
`QuotientChange.normalized_inverse`, transports along the exact pullback derived
comparisons, and cancels their invertible components. Proof-only imports supply
normalization existence, the mate identity, the universe-correct Grothendieck
module-sheaf instance and mate whiskering calculus.

`scalarPullComparison` is expressed as the equivalent inverse-mate component.
The scalar-mate unit identity identifies it with the former scalar transpose of
pullback of the scalar unit. Its signature and mathematical normalization are
unchanged, as are the other scalar-map formulas, public imports and attributes.
`scalarPushMap` now explicitly supplies the comparison object formerly inferred
from `_`, avoiding inference through nested adjunctions. Local irreducibility
annotations keep expensive derived constructions abstract. The auxiliary ringed-site localization instance
is scoped to the existence call. The node records the actual dependencies and
argument. The definition change is recorded in
`coord/changes/J4-free-parameter-scalar-pull-mate.md`.

Both returned consumer failures are repaired in this packet. Each consumer keeps
all signatures, visibility and imports, with only its failed unfolding proof
adapted. Final `lcompile.py --all` exported the item, both adapted consumers,
and unchanged copies of the other three direct importers successfully, with no
warnings. Those unchanged test copies are omitted from the delivery. The tested
additional importers are `Sheaf.AlgebraicGeometry.PerfectScalarChangeModel`,
`Sheaf.Paper.FiniteModelQuotientChartComparison`, and
`Sheaf.Paper.FreeParameterEvaluationCoherence`.

## Proved and sorry left

Closed the one current hole:
`AlgebraicGeometry.ProEtale.FreeParameterEvaluation.scalarPullComparison_isIso`
(node `def-sfb-free-parameter-scalar-maps`). The item now has zero holes.
No holes added, no statements split off, and no holes added to consumers.
The previously proved free-scalar invertibility argument is retained.

## No longer needed

No existing imports, modules or nodes are removed. A fresh K-flat resolution or
single-complex comparison theorem is unnecessary: the existing universally
normalized comparison and its inverse-mate normalization already supply the
argument for every derived object. The unit statement and realized steps stay.

## Where the brief, the DAG or earlier work was wrong

The returned delivery changed `scalarPullComparison` to its equivalent mate form
without adapting two consumers that unfolded the previous adjunct formula.
The mathematical normalization was valid, but the definitional change required
both consumer proofs to be updated in the same packet. This repair does so.
An attempted proof retaining the old data formula typechecked but exceeded the
export time limit; it is not part of this delivery.

The old remaining-step description proposed a fresh K-flat computation. Existing
normalization existence and inverse-mate normalization make that unnecessary.
No new nodes are introduced.

## Forced adaptations

Both affected modules are currently unclaimed. The return supplies the original
compiler failures against the mate definition:

- `Sheaf.SixFunctors.ProEtale.IntegralReductionPullbackNormalization`: line 104,
  `Type mismatch` for `inverseMate_app ...`, whose right side is the old scalar
  adjunct expression. Replace only lines 104–108 by `rfl`: the inverse-mate
  component now is the definition of `scalarPullComparison`.
- `Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization`: line 75,
  `No goals to be solved`. Remove only lines 75–80, the redundant
  `exact scalarSixMateApp ...` after `dsimp only` has closed the equality.

Every existing declaration signature, visibility and import of these consumers
is preserved. The other direct importers need no source change: their use of the
comparison is through its type and invertibility, not its adjunct unfolding.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
