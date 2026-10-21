## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.integralConstructibleCompletionBridge`
with a compiling proof from the existing integral local-finite-presentation and
stratified-perfect comparisons, plus the new ordinary-module comparison
`AlgebraicGeometry.ProEtale.integralSectionLocalModels`. The original signature,
public imports, coefficient constructions and targets are unchanged.

The local-finite-presentation comparison uses a different continuous coefficient
presentation. The proof composes the proved `integralCoefficientIso` helper from
`IntegralConstantModelHeartClosure` with the proved `integerRingSheafIso` helper
from `IntegralCoefficientExtComparison`; scalar restriction and its identity
round trip transfer both constructibility predicates to the original coefficient
ring. These are proof imports using `import all`; no private data appears in a
public signature or definition.

The cohomology argument uses the actual `integralSectionFunctor` and restriction
along `integralDetailedCoefficientComparison.hom`. Their exact derived functors
commute with homology, preserve and reflect boundedness, and match the
`integralSectionDerivedEquivalence` and `integralDetailedTransport` in the existing
statements. It then applies both equivalences of
`integralStratifiedPerfectCharacterization` and its detailed-category clause.

Validation: both sandbox modules compiled together through `lcompile.py --all`
(4.4 seconds and 11.3 seconds in the first complete run; the final packet
compiled again in 4.8 seconds and 11.3 seconds; after the preflight corrections,
both compiled in 4.5 seconds and 11.4 seconds). A further exploratory
compile unfolded the new comparison, selected the original finite stratification
and converted its finite local models to scalar-presentation models. This exposed
the remaining task precisely: transport those scalar cokernels to the ordinary
completed constant realization, including the covering-sieve localization maps,
and reflect this transport. The final packet restores that obligation to a single
public theorem with exactly `:= by sorry`, its own source and full proof in words.

## Proved and sorry left

- Closed the original syntactic hole in
  `AlgebraicGeometry.ProEtale.integralConstructibleCompletionBridge`. Its complete
  assembly proof compiles from the named dependencies.
- Added one hole:
  `AlgebraicGeometry.ProEtale.integralSectionLocalModels`, node
  `lem-sfb-integral-section-local-models`, in
  `lean/Sheaf/Paper/IntegralSectionLocalModels.lean`.
- No holes remain inside the item's module. One original hole was replaced by one
  strictly smaller ordinary-module comparison: this is a decomposition, not a net
  proof gain (closed 1, added 1, net 0). The lower statement has no derived object,
  boundedness, completeness, finite dimension, invertibility or Tor conclusion.
  Existing imported holes are not counted as holes added by this packet.

The new statement was checked on zero modules, zero-rank presentations, torsion
scalar modules and the empty scheme. The normalized ring comparisons and exact
functors preserve these cases. It requires scalar matrices and does not identify
arbitrary coefficient sections with constant scalars.

## No longer needed

Removed direct proof imports:
`Sheaf.Paper.ContinuousIntegralCoefficients`,
`Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`,
`Sheaf.SixFunctors.ConstructibleOpenClosedRefinement`,
`Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle`,
`Mathlib.Topology.NoetherianSpace`, and
`Sheaf.Paper.IntegralLfpLocallyFreeResolution`.
`Sheaf.Paper.CartesianCoefficients` is retained because preflight identifies it
as a unit-route import.
`IntegralStratifiedPerfectCharacterization` remains, now as `import all` for its
proved isomorphism-invariance helper. All other new proof imports name declarations
used by the proof. Existing public imports are retained.

The item's replacement argument does not directly use these old planned nodes:
`def-weil-pbc-continuous-integral-coefficients`,
`lem-fix-constructible-open-closed-refinement`,
`lem-sf-derived-ses-triangle`,
`lem-sfb-noetherian-space-compact-subsets`,
`lem-weil-pbc-integral-lfp-locally-free-resolution`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`, and
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`.
The proved lfp-to-constant-model theorem replaces the resolution and cone argument.
The cohomological definitions allow degree-dependent finite stratifications, so no
common refinement is needed. The new heart comparison still uses the existing
finite-constant-model and Cartesian coefficient interfaces. Coefficient-limit and
Noetherian results can remain necessary inside imported dependencies; this packet
withdraws no module and makes no claim that they disappear from the global target
closure. The item's obsolete direct tool approvals are removed; the stratified-
perfect approval is retained.

## Where the brief, the DAG or earlier work was wrong

The original step 7 said the completed characterization's scalar-model condition
was exactly the internal finite-constant-model condition. In Lean they use distinct
module encodings, scalar-module encodings and cover conventions: the former uses
`SheafOfModules`, `PbcIntegralRing` and covering sieves, whereas the latter uses
internal module objects and scheme covers. The equivalence is mathematically
correct but is a separate presentation comparison, not definitional equality.
The new node records that missing obligation at the level of individual module
sheaves; the derived assembly is fully formalized here.

Likewise, the existing proved integral lfp comparison has WithAbs coefficients.
Applying it directly to the item's spectral coefficient module fails conversion;
the proof now explicitly transports across the two proved ring isomorphisms.
No statement or definition was weakened or repaired. There are no forced consumer
adaptations and no change records are needed. The first preflight detected an
extra global `open` command; that command was removed and the exact-functor
classes are now fully qualified. Elaboration options are scoped to the theorem.
The same preflight required a LeanSearch record in addition to LeanFinder/Loogle
and source grep; this search was run and added to the new node.

## New nodes

`lem-sfb-integral-section-local-models` realizes the ordinary coefficient-presentation
part of step 7 of the original item. It compares finite scalar local models of a
single module sheaf under the fixed normalized section-action and ring-restriction
functors, and has its own source in Bhatt--Scholze Definition 6.8.10 and the
coefficient conventions used in Proposition 6.8.11(3). The proof in words specifies
finite scalar cokernels, their normalization on positive quotients, restriction
to strata and slices, and the two cover conventions. This statement is strictly
smaller than the original derived equivalence, and the original theorem is proved
from it by nontrivial exact-functor cohomology and boundedness arguments and the
existing completed characterization. The unit route is retained.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
