## Worker report

The item is stated by `AlgebraicGeometry.ProEtale.projectionComparison_etaleOrigin` in
`lean/Sheaf/AlgebraicGeometry/ProjectionComparisonEtaleOrigin.lean`.  It binds the finite
field datum `D`, the prime `l` with `_hl : l ≠ D.p`, the finite-dimensional coefficient
extension `E`, positive level `n`, finite-type `D.k`-schemes `X,Y`, and the separated,
locally-finite-type, quasi-compact morphism `f`, together with its fixed
`Compactification f` value `c`.  The two derived complexes are the recorded
`Etale.DerivedCategoryModule` values `M` and `H`; `_hM` and `_hH` are their bounded
constructibility hypotheses and `_hTor` is the stated finite Tor-amplitude existential.
The theorem concludes with the canonical existential bounded-below witnesses and the
projection-comparison equation.

The full equation and its canonical target transport are in the helper node
`def-smooth-purity-projection-comparison-equation`, imported from
`Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation`.  Its
`ProjectionComparisonEquation` field is the exact equality of the pro-etale projection
route (compactification projection, pullback/tensor target isomorphism, and canonical
compact-support site comparison) with the etale route (comparison map, inverse tensor
comparison, and etale projection map).  `projectionComparisonConclusion` packages the
same existential witnesses and equation at the finite coefficient ring
`Padic.coefficientExtensionRing l E n`.  The helper also defines the positive-level
finiteness instance, the canonical pullback comparison isomorphism, the tensor target
isomorphism, and the tensor target abbreviation used in the witness.

Each clause of the node statement is rendered as follows.  The finite field and
characteristic data are `WeilConjectures.FiniteFieldDatum D`; `l`, `_hl`, `E`, `n` and
`Fact (1 ≤ n)` are the first binders.  The finite-type schemes over `Spec (of D.k)` and
all morphism properties are the `Over`, `LocallyOfFiniteType`, `QuasiCompact`,
`IsOver`, and `IsSeparated` instance binders.  The fixed compactification is `(c :
Compactification f)`.  The ordinary/pro-etale comparison, compact-support direct image,
derived tensor, and projection maps are the recorded declarations used in the helper:
`comparisonUpperStar`, `compactSupportSiteComparison`,
`rightDerivedLowerShriekOfCompactification`, `projectionMapOfCompactification`,
`Etale.projectionMapOfCompactification`, and
`derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`.  The target transport is
`projectionComparisonTargetIso`; its pullback part is
`projectionComparisonPullbackIso`.  The conclusion is exactly
`projectionComparisonConclusion D l _hl E n f c M H _hM _hH _hTor`, whose explicit body is
the existential over the two `DerivedCategory.TStructure.t.plus` witnesses and the
`ProjectionComparisonEquation` equality.  Naturality and the absence of smoothness or
exceptional-pullback assumptions are represented by the natural transformations used in
that equality; no such extra typeclass is introduced.

Dependency declarations used (all imported by the helper) are:

- `Sheaf.Paper.FiniteFieldFiber` — `WeilConjectures.FiniteFieldDatum`.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite` —
  `Padic.coefficientExtensionRing` and its finite instance.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes` — the bounded constructibility
  predicates used by the theorem hypotheses.
- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison` —
  `compactSupportSiteComparison`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal` —
  `derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection` —
  `rightDerivedLowerShriekOfCompactification` and
  `projectionMapOfCompactification`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection` —
  `Etale.projectionMapOfCompactification`.
- The two flat-module imports provide the `UpperStarPreservesFlat` instances required by
  the comparison and pullback constructions.

Edge cases checked against the statement and source proof are zero complexes, empty
schemes, identity open or proper factors in a compactification, and the absence of any
local-freeness, smoothness, or exceptional-pullback hypothesis.  The finite level uses
`Fact (1 ≤ n)` exactly, so the prohibited `n = 0` case is excluded by the node; the prime
condition is represented by `Fact l.Prime` and `_hl`.

Searches retained and checked on resumption:

- `msearch.py` LeanSearch, "canonical fixed compactification projection comparison
  equation between etale and proetale compact support": eight unrelated hits on
  compactly supported continuous maps, Stone-Cech and condensed constructions.
- `msearch.py` LeanFinder, "canonical compactification projection comparison equality
  derived category": eight hits, including abstract completions, Stone-Cech,
  `CompHausLike.LocallyConstant.sigmaComparison_comp_sigmaIso` and the generic
  `Functor.mapDerivedCategoryFactorsh_hom_app`; no compact-support equation.
- `msearch.py` Loogle, "projectionMapOfCompactification, compactSupportSiteComparison":
  zero hits, unknown Mathlib identifier `projectionMapOfCompactification`.
- Exact-name `rg` for the equation/conclusion in DAG, side Lean, upstream and Mathlib:
  no matches. `blueprint_refs.py search "projection comparison"` returns only
  `lem-coef-finite-free-extension`, whose subject is scalar extension.
- Broader upstream `projection.*[Cc]omparison|[Cc]omparison.*projection` finds
  `LowerStarProjectionComparison` (the proper-factor square) and `ProjectionFormula`
  (invertibility of the compact-support projection), not this full fixed-compactification
  equality. These are existing primitives for the proof, not duplicates of this item.

The helper node is new because no Mathlib or upstream declaration supplies the fixed
compactification equation or its canonical target transport.  No `STATEMENT-DISPUTED`
flag or node fault remains.

## New nodes

`def-smooth-purity-projection-comparison-equation` records the missing canonical
fixed-compactification equality and the finite-level existential conclusion as a
definition node.  Its module is
`Sheaf.AlgebraicGeometry.ProjectionComparisonEtaleOriginEquation`; its source is the
first paragraph of the blueprint proof at the Stacks 0E48 comparison square.  The
Mathlib, upstream, and project searches above found no existing declaration, so the item
adds this helper node to `stmt_deps`.

## Dependency modules

`def-compact-support-direct-image-detailed`: the intrinsic compact-support interface uses
coefficients in the scheme universe and intrinsic ringed-site endpoints. Its existing
fixed-ring module-sheaf presentation is repaired to the canonical upstream
`rightDerivedLowerShriekOfCompactification` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek`.
It is the same proper direct image after exact open extension at c.

`def-weil-derived-tensor`: the recorded intrinsic ringed-site tensor has SheafOfModules
endpoints, while the comparison and projection interfaces use ModuleCat-valued sheaves.
The repaired record uses the existing `AlgebraicGeometry.ProEtale.derivedTensor` in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`, specialized to
`ModuleCat.{u+1} A`. Both are ordinary uncompleted K-flat total derived tensor.
This is a presentation repair; the intrinsic tensor has since been generalized in
universes and no universe restriction is asserted here.

`def-exchange-projection` needs no dependency repair in this packet. The equation uses
its specified finite projection construction, `projectionMapOfCompactification`, through
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection`.
That construction has the same proper-counit/open-projection/composition formula as the
historical module used by the recorded `Sheaf.Paper.ExchangeProjection`. The saved
replacement of that latter module has been removed from the packet, together with its
unnecessary dependency-node delta. The published module keeps all of its public imports.

The saved `lem-sf-class-compact-support-comparison` repair was removed: its single-import
repair has already landed in the current library under Q78. This delivery imports that
published module unchanged.

## Statement corrected

No statement correction was needed.


Self-check on resumption: all four initial wrapper file checks passed. Preflight found
malformed helper metadata/citations, two signature mismatches, the stale comparison
repair, and missing dependency descriptions. The helper now cites each notion explicitly,
records the correct blueprint ancestor/via and split status, and has transparent bodies
marked irreducible for elaboration rather than opaque propositions. The pullback helper
now has its source/blueprint docstring. No mathematical statement was changed.


## Repair of return L (immutable head 27e156147b9e)

The initial required dry run of the retained packet passed at f4b7b7cfc2. The independent
return nevertheless identifies a real import-interface regression in its replacement of
`Sheaf.Paper.ExchangeProjection`: three consumers use declarations exported by its
historical imports. The repair removes that replacement and its dependency-node repair
from this delivery, preserving the published module and every public import byte for byte.
This also preserves `projectionMapOfCompactification` for
`Sheaf.AlgebraicGeometry.FiniteCompactProjectionFormula`, and
`rightDerivedLowerShriekOfCompactificationBaseChangeMap` for both
`Sheaf.Paper.CohomologicalSmoothness` and `Sheaf.Paper.CompactSupportCoefficientChange`.
Those three modules therefore retain the same import environment and need no adaptation.

Self-check: read the current server source with `scompile.py --source
Sheaf.Paper.ExchangeProjection`, compared its imports with the saved replacement, and
checked that neither delivered Lean module imports the replaced module. Both new modules
continue using the canonical upstream projection and comparison constructions directly.
The theorem signature, hypotheses, target transports, equation, and real definition bodies
are unchanged. This is a substantive removal of the returned import-pruning delta, not an
unchanged re-push. Validation after repair: `scompile.py Q98 lem-pur-projection-comparison-etale-origin`
compiled both delivered modules separately, with no errors or warnings. The equation
helper passed in 13.5 seconds and the theorem module in 3.5 seconds on the server; the
private overlay and sandbox checks passed too. JSON layout, explicit binding options,
line width, and the absence of an ExchangeProjection replacement were checked locally.
A fresh delivery dry run follows before pushing.

## Second reading by Q98

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
