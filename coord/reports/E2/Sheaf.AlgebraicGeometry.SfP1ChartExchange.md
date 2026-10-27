## What changed

Replaced the hole in `AlgebraicGeometry.Etale.SfP1Transport.chartExchange` with a
complete Lean argument from canonical derived mates, chart pasting, normalized
Tate-line composition, and the new lower lemma `chartMap_compHom`. The exchange
and line-composition calculations are proved locally. The remaining lemma only
normalizes the two direct-image composition factors in the chart-map definition.
The item's statement, definitions and public imports are unchanged.

Private proof imports added to the item:

- `WeilConjectures.SixFunctors.Etale.Derived.CompactificationRefinementLowerStar`
  for composite-adjunction counits and inverse-image associativity.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness` for normalized
  line transport and its canonical composition law.
- `Sheaf.AlgebraicGeometry.SfP1ChartMapComposition` for the isolated final step.

Proved private comparison calculations follow the existing proved helpers in
`AffineTraceLineOpenCounitBaseChange` and `FiniteP1TwistedUnitBaseChange`; neither
large module is imported. Updated the item's node to follow the Lean proof.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.SfP1Transport.chartExchange`
(node `lem-sf-p1-chart-exchange`) by reduction. No sorry remains in the item.
Every private helper is proved, including exchange pasting, comparison transport,
and shifted line composition. The N=0 case is proved on the empty small etale site.
Both files compiled in import order without warnings: 32.0 s for the new lemma
module and 52.8 s for the item, each below the 60 s limit.

Added one hole:
`AlgebraicGeometry.Etale.SfP1Transport.chartMap_compHom`
in `Sheaf.AlgebraicGeometry.SfP1ChartMapComposition`
(node `lem-sf-p1-chart-map-composition`). This is a decomposition: 1 original hole
closed, 1 lower hole added, net 0; it is not reported as a completed proof without
new obligations. No hole was added inside a definition. Existing finite-twist
pullback and normalized-transport dependency obligations are not claimed closed.

## No longer needed

Removed `lem-sfb-ringed-derived-monoidal-comparisons` from the item's proof
dependencies: canonical source-library comparisons and direct mate calculations
suffice. No import of `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons` is used.
The diagonal Kummer component theorem is not used; its module remains necessary
for the chart-map definition. Its node remains a statement dependency and a
definition dependency of the new normalization lemma.

Removed exploratory private imports of `BaseChangeCube`, `MapDerivedCategoryMate`,
`LeftDerivedFunctor.SingleFunctor`, `Shift.ExactFunctor`, and
`CupProductCoherence`. Pullback associativity is used directly; the middle three
APIs are already exposed by existing imports. The new lemma imports the existing integral-transport context (for its cached
derived-category instances) and `LowerStarProjectionComp` for its composition map. No existing module
is withdrawn, and no unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The original ringed monoidal dependency was
unnecessary. Positivity of N cannot be silently assumed: invertibility of zero
forces the base to be empty, which proves the missing N=0 line-coherence case.

The remaining normalization is mathematically the source identity
`rightDerivedLowerStarComp_hom_comp_congr_hom`, evaluated and composed with the
unit and shifted-line map. Direct implementations elaborate quickly but exceed
the limit in kernel checking when the original chart definition is expanded.
Profiling and expression comparison locate this in the large derived-functor
expressions with generated instance proofs. Explicit composition equalities,
defining equations, controlled expansion and cached instances were tried; no
diagnostic options or cache experiments are included in the delivery. The
original chart definition belongs to the F1-held module
`FiniteP1DiagonalKummerComponentFormula`; this delivery changes no shared interface
and makes no edit to that module. The exact remaining equality, with its complete
mathematical proof and edge cases, is exposed as the lower obligation.

## New nodes

`lem-sf-p1-chart-map-composition` states the normal form of the chart-map definition
as a unit, `rightDerivedLowerStarCompHom`, and the line comparison. It contains no
product or projective exchange assertion and needs no finite-coefficient
hypothesis or line-composition law. It is strictly the final bookkeeping part of
the original argument. Mathlib searches found generic evaluation/comparison APIs;
blueprint searches for chart composition and adjunction composition found no
existing matching node. It inherits the item's unit and source paragraph. No
change record is needed because no other existing module or node was changed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
