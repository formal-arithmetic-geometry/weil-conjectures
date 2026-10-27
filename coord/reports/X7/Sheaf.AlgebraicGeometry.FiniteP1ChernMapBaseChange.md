## What changed

Proved `AlgebraicGeometry.Etale.ordinaryFiniteP1_chern_map_baseChange` without changing its
signature or public imports. The proof uses the existing arbitrary-scheme naturality of
`Scheme.rootsOfUnityCohomologyMap_kummerδ₁` and
`Scheme.gmCohomologyMap_toCohomologicalPicardGroup`, together with
`ProjectiveSpace.pullbackMapTwistIso` for O(1). The arbitrary-base Ext realization underlying
`ordinaryFiniteClass_bijective_arbitraryBase` identifies the specified derived morphisms.

The private helpers prove the coefficient-root square from `line_normalization` at 1, identify the
specified roots comparison by its normalization, and prove naturality of exact forgetting and the
integral generator on Ext representatives. Proved private identities relate the cached canonical
Ext equivalence to composition, exact functor transport and derived inverse image. A general
categorical cancellation identity handles the unit and shifted-line comparisons without expanding
their concrete derived-category data. A proved identity for arbitrary functions and equivalences
transfers Ext naturality to class naturality. Public class injectivity identifies the normalized
arrow, and cancellation of the canonical unit comparison gives the square.

The two unclaimed definition modules OrdinaryFiniteP1Kummer and OrdinaryFiniteP1Arrows are adapted
to cache the canonical Ext equivalence against the existing degree-zero functor and expose its
comparison equations. The canonical functor is constructed with its named degree-zero object as
its explicit object field; its maps and functor laws remain the canonical single-degree ones. The new equivalence is Mathlib's actual
Ext.homEquiv, with endpoints using the existing cached embedding. The generic Ext realization
formula is shared by the original morphism realization and the cached one. Existing concentration
instances unfold the same canonical degree-zero object. Both modules reuse the sheafification and Grothendieck
proposition instances already stored in DerivedCategoryModule, so the canonical localization is
constructed with matching arguments before taking object maps. The Kummer module names that
same chosen canonical localization with `ordinaryFiniteDerivedCategoryInstance` and uses it
locally, before taking its projections; its body is the existing canonical construction. Every object, class map and
comparison unfolds to its original formula; no existence witness or new mathematical assumption is
introduced. The change record is `coord/changes/X7-finite-p1-degree-zero-interface.md`. Targets
using the definitions are reopened for the independent statement review. No proof is moved to
another module for compilation, and no new Lean module is added.

The X5 comparison repair landed during this session. Its constant unit and public import of
RelativeKummerExchangeGenerators are preserved. The unit comparison now explicitly uses the
cached single-degree factorization of the same canonical genericConstantIso value. This is
necessary because conversion from the generic wrapper to the cached interface takes 98 seconds.
The cached functor, exact comparison and constant-sheaf comparison unfold to the original data. The currently
quarantined concentration consumers retain their archives and dependencies; none is withdrawn.

The existing P1 Kummer-class definition now specializes the explicit arbitrary-scheme construction
`ordinaryFiniteKummerClass`. Its body is exactly the original coefficient-map image of the Kummer
boundary of the Picard class. This caches the construction before the projective-space
specialization, with no change to its data or public type. The main proof first proves the square
for arbitrary Picard classes with specified pullback equality, then specializes to O(1).

Complete equation lemmas expose the realization, the canonical equivalence, and the comparison factorizations:
`ordinaryFiniteClass_extHomEquiv`, `ordinaryFiniteExtHomEquiv_eq`,
`ordinaryFiniteSingleExactPullbackIso_eq`, `ordinaryFiniteUnitPullback_eq`, and
`ordinaryFiniteShiftedLinePullback_eq`, and `ordinaryFiniteP1ChernSpec_iff`. These are proved from the definitions, with no new
mathematical assumption or proof obligation.

The already proved private `coefficient_unit` is reused by `import all
Sheaf.AlgebraicGeometry.SupportedDerivedUnitForget`; it applies to every scheme morphism, despite
that module's other theorems concerning closed immersions. The public
`ordinaryFiniteClass_bijective_arbitraryBase` supplies class injectivity. Its unclaimed module
uses the same cached equivalence in the final line of its proof, with the existing statement and all other proof steps unchanged. It also registers
the same two proposition instances before its private helpers; no instance is exported.

Added only proof imports: OrdinaryFiniteClassArbitraryBase, GmPicardPullback,
Ext.MapExactFunctorConj, SupportedDerivedUnitForget, with no import of
ExtendScalarsCohomologyPullback. Updated the item's proof steps and dependencies. The three new
DAG records attach two existing source-library theorems and one Mathlib leaf; they add no Lean
module or statement.

The current X5 consumers are checked against this interface. Necessary proof adaptations in
unclaimed modules preserve every public signature: FiniteP1TwistedUnitBaseChange locally exposes
the cached single functor and reuses the two canonical proposition instances;
OrdinaryFiniteClassScalarFaithfulness unfolds the new Ext helper where its old proof unfolded
the realization; VectorIntegrationIdentityUnit uses the comparison equations;
FiniteP1ChernAdjunctMate applies the existing ordinaryFiniteUnitPullback_comp to the actual
cached comparisons, instead of converting them to genericConstantIso. Its mate argument is
unchanged and the replacement DAG dependency is recorded. The scalar-adjunct and Kummer-maps consumers remove
references to two auxiliary proof declarations eliminated by instance sharing. These adaptations
introduce no holes or mathematical assumptions.

## Proved and sorry left

Closed the item's single hole: `AlgebraicGeometry.Etale.ordinaryFiniteP1_chern_map_baseChange`.
One of one original holes closed; zero holes added; zero split off. No `sorry` remains in any
delivered Lean file. All private helpers are proved. The two canonical definition interfaces and
the unclaimed arbitrary-base bijectivity consumer are adapted as described above, with zero holes.
No adopted source-library declaration or target statement is changed; the assigned theorem
signature is verbatim unchanged.

The final coherent compile of all ten delivered Lean files passes the per-file compile gate.
The fresh axiom audit of ordinaryFiniteP1_chern_map_baseChange reports exactly propext,
Classical.choice and Quot.sound. Profiling and audit commands are removed from the final files.
The complete main proof remains in its assigned module.

All 17 targeted consumer checks passed: the six adapted consumers above, plus
OrdinaryFiniteFibreHomologyComparison, OrdinaryFiniteGeometricPointHomology,
OrdinaryFiniteP1FibreHomologyCard, ProjectiveLineTateCoefficientGenerator,
OrdinaryFiniteClassComparison, OrdinaryFiniteClassInjectivity, OrdinaryFiniteUnitPullbackHom,
OrdinaryFiniteUnitPullbackComp, VectorIntegrationLocalTraceCompatibility,
VectorTraceGeometricDescent and OrdinaryFiniteP1DecompositionMaps. Unchanged test copies are
omitted from the packet. Quarantined consumers remain preserved at their recorded paths;
this delivery neither restores nor withdraws them. The coherent compile includes all six adapted
consumers against the final definition interfaces. deliver3.py performs the final preflight.

## No longer needed

The new proof does not use these four former planned dependencies:

- `lem-weil-pbc-projective-space-standard-charts`
  (`Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts`): the actual O(1)
  pullback isomorphism already exists.
- `def-nagata-effective-cartier-ideal`: constructing the infinity Cartier ideal is
  unnecessary for naturality of the already specified Kummer class.
- `def-pc-divisor-line-bundle`: no conversion from a divisor to O(1) is required.
- `lem-asd-ordinary-supported-kummer`
  (`Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer`): the ordinary Kummer boundary is
  already natural for arbitrary scheme morphisms.

These are removed as mathematical proof dependencies of this node. No Lean import from the
original module was removed: it had only its statement import. The proposed proof import
ExtendScalarsCohomologyPullback is also unused: Mathlib Ext.mapExactFunctor_hom and naturality
suffice directly. The private integral normalization helper still imports
SupportedDerivedUnitForget and therefore its existing transitive supported-Kummer definitions
remain in the import closure. No global module withdrawal or unreachable-module claim is made.

The adapted mate module also drops its proof imports of RelativeKummerExchangeGenerators,
LeftDerivedUpperStarSingle and UpperStarConstantSheafComp. The proved unit-composition API
already supplies the required square. The arrows module retains its existing public import of
RelativeKummerExchangeGenerators, so this is no global withdrawal.

## Where the brief, the DAG or earlier work was wrong

The planned hyperplane calculation is unnecessary. The adopted library already proves
Kummer-boundary naturality and Picard-class naturality for arbitrary schemes, with no Noetherian,
quasi-compact or quasi-separated hypothesis. The normalization fields of the transport suffice to
identify their coefficient maps with the ones in this statement. This also covers the empty scheme
and the zero coefficient ring; no nonzero generator or field trivialization is chosen. The unit's
base-change route is preserved.

The existing blueprint ancestor script returns no ancestor because earlier stage-3 `created.item`
fields contain module names. The new records name the actual blueprint ancestor
`det-sp-tower-p1-adjunction`, as the reviewed parent record does, and identify the base-change
step precisely. The item itself also has an inherited `blueprint.from.node` pointing to the
created node `lem-sp-finite-p1-chern-adjunct-base-change`, which the blueprint checker rejects as
a non-blueprint node. That field is retained because stage-3 node ownership excludes blueprint
metadata; it needs a maintainer correction. Searches of the full blueprint found no
arbitrary-scheme Kummer or Picard pullback node. The existing curve-only Picard pullback node does
not apply to the arbitrary base schemes in this item.

## New nodes

`lem-sp-kummer-boundary-arbitrary-pullback` records the existing proved source theorem
`AlgebraicGeometry.Scheme.rootsOfUnityCohomologyMap_kummerδ₁` from
WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnityPullback. This is ordinary Kummer boundary
naturality alone, independent of projective space, scalar coefficients and the derived Chern
representative.

`lem-sp-picard-cohomology-arbitrary-pullback` records the existing proved source theorem
`AlgebraicGeometry.Scheme.gmCohomologyMap_toCohomologicalPicardGroup` from
WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback. It identifies pullback of the Picard
cohomology class with the class of the pulled-back invertible module on arbitrary schemes. All
three records have `lean.existing: true`; none introduces a hole.

`lem-sp-derived-pullback-ext-hom` is the Mathlib leaf
`CategoryTheory.Abelian.Ext.mapExactFunctor_hom` from
Mathlib.Algebra.Homology.DerivedCategory.Ext.Map. It is the formal compatibility of an exact
functor on Ext with its derived morphism under the canonical single-object and shift comparisons.
Naturality and the transported-shift formula complete the left-derived comparison in the item
itself. The larger source Chern-pullback module is unnecessary.

The constructed Ext equivalence, generic Ext realization, arbitrary-scheme Kummer class,
O(1) Picard class and proved specification characterization are attached to the existing
definition node `def-asd-ordinary-finite-p1-kummer-class`. They are complete definitions, not new
proof obligations. The existing arrows node records the canonical unit-comparison factorization.

## Second reading by X7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
