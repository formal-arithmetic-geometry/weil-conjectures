## What changed

Proved `AlgebraicGeometry.Scheme.rationalRealizationPullbackModel` in
`Sheaf.Paper.RationalRealizationPullbackComparison`. First apply
`cbcDatumOrdinaryTransport (pbcIntegralDatum l E) h` to the realized input. Then
compose with the existing, proved private helper
`integralConstantDerivedPullIso (pbcIntegralDatum l E) h` from
`Sheaf.Paper.ExtensionZeroPerfectModelTransport`, accessed by a proof-only
`import all`. The latter is a natural isomorphism for every scalar complex;
perfectness is therefore unnecessary for this proof, and the theorem's original
signature is retained verbatim. The comparison applies to arbitrary schemes and
morphisms, including the pro-etale charts in the statement.

The helper is constructed by the constant-module/global-sections adjunction,
the scalar-normalized ordinary module adjunction, and exact derived descent.
The first transport is the universal-counit-normalized comparison between the
published actual pullback and the datum's exact derived presentation. The Lean
proof composes these two specified isomorphisms; it chooses no new data from
mere existence.

Added a first proof step and its two dependencies to the item's existing DAG
node, documenting this shorter route for the model clause. The seven existing
steps remain the plan for the main theorem, which is unchanged.
No definitions, public signatures, public imports, target statements or source
library modules change. The blueprint unit's statement and steps are retained.

The proof compiled remotely before import pruning (11.3 seconds, exit 0), and
final validation is run through lcompile.py and deliver3.py. The two new DAG
edges were checked for a path back to this item; neither forms a cycle.

## Proved and sorry left

Closed 1 of the item's 2 original holes:
`AlgebraicGeometry.Scheme.rationalRealizationPullbackModel`
(node `lem-per-rational-realization-pullback-comparison`).

The one remaining hole is
`AlgebraicGeometry.Scheme.rationalRealizationPullbackComparison`
(the same existing node). Its whole proof remains `by sorry` and its original
seven-step natural-language proof remains in the docstring. This is a partial
module delivery: the completed/ordinary integral restriction, normalized
coefficient and tensor comparison, and raw fraction descent record are not
claimed proved. No holes were added and no statements were split off.

## No longer needed

Removed these unused private imports from the item:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.CategoryTheory.RingedDerivedPullbackLinear`
- `Sheaf.Paper.OrdinaryPullbackStratifiedModels`
- `Sheaf.Paper.PbcIntrinsicTowerComplete`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.Paper.ReductionPullbackDerivedTower`
- `Sheaf.Paper.RingedTopoiDerivedPullbackIndependent`
- `Sheaf.Paper.KFlatRingedToposPullback`

The model proof needs only the existing constant-realization pullback helper and
ordinary-presentation transport. In particular it does not require choosing a
bounded finite-projective representative, proving K-flatness anew, or following
the ordinary stratified-model presentation. The original proof dependencies of
the main theorem remain in the DAG because that theorem is still open. No
node or module is withdrawn, and no target-closure module pruning is claimed.
All four original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The model theorem's proposed bounded finite-projective/K-flat computation is
unnecessary: an already proved helper establishes the required constant-model
isomorphism for every scalar complex. The two existing pullback presentations
are not definitionally the same, so using the explicit ordinary transport is
necessary. This does not replace or identify the strict completion unit and
does not resolve the main theorem's separate specified-unit normalization.
No mathematical error in that main statement is asserted.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
