## Worker report

The module Sheaf.AlgebraicGeometry.IntegralDerivedExtensionComparison states the
item on the actual continuous internal coefficient objects, with its canonical
termwise and triangle comparisons. Only the item's lean record changes. There
are no new nodes, dependency-node files, dependency modules or statement changes.

The seven instance caches reuse the existing integral/field MonObj and IsCommMonObj
structures, the coefficient IsMonHom instance, and the source module category's
MonoidalCategory and Abelian structures. Every cache body is inferInstance, with
its full existing data; these are specializations of recorded definitions and
instances, not new mathematical facts or choices. No file-local instances are used.

Each hypothesis and clause is rendered as follows:

- The prime is `(ℓ : ℕ) [Fact ℓ.Prime]`; the finite embedded extension with its
  induced norm is `(E : PadicAlgCl.FiniteIntermediateField ℓ)`.
- `(X : Scheme.{u})` is the scheme and `[TopologicalSpace.NoetherianSpace X]`
  is explicit on every declaration. The universe u is bound explicitly, the
  coefficient universe is u+1, and the original small pro-etale site is retained.
- The coefficient morphism is exactly `padicIntegersToPadicSubfield X ℓ E`.
  T is exactly `Mod.extendScalars` of this morphism. This coefficient map is
  definitionally `coefficientMap (CondensedRing.integralScalarMap ℓ E.1) X`:
  the two constructions postcompose continuous functions with the integral
  subtype inclusion and use the same inverse image from the profinite point.
  A separate scratch compile checked the equality by rfl.
- `integralExtensionDerived` caches the LEFT FUNCTOR of the recorded
  `Mod.derivedExtendMapDerivedCategoryAdjunction`. Its transparent lambda
  returns the functor index F, not any data selected from an existence claim.
  The adjunction's left index is literally the specified
  `(Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor`.
  This is definitionally `CondensedRing.integralScalarExtension ℓ E.1 X`;
  the second rfl scratch check verifies the full functor equality, including
  all coefficient, category and structure arguments. These identifications
  require no additional theorem assumption.
- `integralExtension_exact` gives preservation of finite limits by T. The
  upstream `Mod.extendScalars` additive instance and
  `Mod.preservesFiniteColimits_extendScalars` give the other two exactness
  clauses for this same T; the latter follows from `extendRestrictAdjunction`.
- `integralExtensionDerivedCounit` is the EXISTING
  `Functor.leftDerivedFunctorCounit` of this actual T. The named theorem
  `integralExtensionDerived_isLeftDerived` states its existing left derived
  universal property. Its proof docstring records the K-flat construction and
  generic instance that will prove this setup property in stage 3.
- `integralExtensionTermwiseComparison` is the actual canonical isomorphism
  L ≅ T.mapDerivedCategory. Its body is Functor.leftDerivedUnique applied to
  L, its own counit, the termwise functor and its invertible counit. This is
  exactly the construction in leftDerivedFunctorIsoMapDerivedCategory,
  without repeatedly elaborating the concrete graded tensor interface.
  It uses neither an arbitrary isomorphism nor a Nonempty choice.
- `integralExtensionCommShift` transports the termwise shift to L by
  `Functor.CommShift.ofIso` along the inverse of this canonical comparison.
  At every integer shift its component is alpha at K[n], the termwise
  shift, and the shifted inverse of alpha. `integralExtension_triangulated`
  states that L preserves distinguished triangles for this structure.
  Mathlib's existing Functor.IsTriangulated additive instance supplies
  L.Additive (Triangulated/Functor.lean:237).
- C and D are the existing boundedConstructible full subcategories for the
  pulled-back integral and field rings. Their inclusions are exactly
  `(boundedConstructible ...).ι`. The imported landed instance
  `isTriangulated_boundedConstructible_padicIntegers` supplies the inherited
  triangulated integral source, including shifts, triangles and inclusion.
  No derived completeness condition is introduced.
- F is exactly `boundedConstructibleExtendScalars X ℓ E`.
  `boundedConstructibleIntegralExtension_additive` states its additivity.
- Beta is exactly `boundedConstructibleExtendScalarsCompatibility X ℓ E`,
  whose components are identities. The ambient shift on Fj is explicitly
  transported from iL along beta by
  `boundedConstructibleIntegralExtensionAmbientCommShift`.
  `boundedConstructibleIntegralExtensionCompatibility_commShift` states
  compatibility of beta with this shift in every integer degree.
- `boundedConstructibleIntegralExtensionTriangleComparison` is precisely
  `Functor.mapTriangleIso beta`. Its three vertex components are beta; the
  first two squares are naturality and the last square uses the specified
  shift compatibility. It identifies whole triangles, including the last
  arrow, without assuming that the field constructible category is triangulated.
- `integralDerivedExtension_comparison` states `(F ⋙ j).IsTriangulated`.
  Thus every distinguished C-triangle has distinguished Fj image. The
  preceding specified triangle comparison identifies it with its iL image,
  which is distinguished by the inherited inclusion and ambient L exactness.

Dependency declarations read and used (including proof-plan imports):

- WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization:
  padicIntegersToPadicSubfield, boundedConstructibleExtendScalars,
  boundedConstructibleExtendScalarsCompatibility, and the actual point inclusion.
- WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars and
  ChangeOfScalarsSquare: Mod.extendScalars, its additive instance,
  extendRestrictAdjunction and preservesFiniteColimits_extendScalars.
- WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars:
  derivedExtendMapDerivedCategoryAdjunction, with the actual total left derived
  functor as its left index; LeftDerivedFunctor.Defs: leftDerivedFunctorCounit
  and the corresponding universal-property instance.
- Sheaf.Paper.ContinuousIntegralCoefficients: continuousIntegers, integralCoeff,
  integralScalarMap, integralScalarExtension and integralConstructible.
- Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructible: the original general
  boundedConstructible, BoundedConstructible and membership declarations.
  They are already listed in the unchanged Q36 dependency record and publicly
  re-exported by CoefficientBoundedConstructibleProEtale. Importing the smaller
  general interface directly therefore needs no rebind of that record.
- Sheaf.AlgebraicGeometry.PadicIntegersBoundedTriangulated:
  isTriangulated_boundedConstructible_padicIntegers. This is exactly the source
  predicate here; its landed proof uses integralConstructible_serre and the
  generic bounded-constructible triangulation theorem.
- Mathlib.CategoryTheory.Triangulated.Pretriangulated, Triangulated and Functor:
  the inherited category structures, Functor.IsTriangulated, its Additive
  instance, and mapTriangleIso. Shift.CommShift: CommShift.ofIso.
- WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory:
  the canonical leftDerivedFunctorIsoMapDerivedCategory formula, which the
  delivered comparison realizes directly with leftDerivedUnique.
- Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor: mapDerivedCategory,
  mapDerivedCategoryFactorsh, and its additive, shift and triangulated instances.
- Proof-plan imports: Sheaf.Paper.ContinuousIntegralScalarExact
  (integralScalarExtension_exact), Sheaf.Paper.IntegralConstructibleSerre
  (integralConstructible_serre), the UpstreamExtra ProEtaleModule.DerivedCategory
  module (isTriangulated_boundedConstructible_of_serre),
  Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
  (rightExactFunctor_le_additiveFunctor), and
  Sheaf.CategoryTheory.DerivedCategory.LeftDerivedTotalTensorExact
  (leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory).

Source: Bhatt--Scholze, Section 6.8, Definition 6.8.10, Proposition 6.8.11(1),(3),
and the preparatory comparison used by Proposition 6.8.14(2). The current
main-20261015 blueprint uses this preparation in the constructible scalar
extension/rationalization unit. Every postponed theorem has its source,
blueprint ID and complete natural-language proof in its docstring. Every
constructor has real data; every delivered theorem proof is sorry.

Edge cases: X empty, zero objects and zero complexes are allowed. All integer
shifts occur, including zero and negative degrees. The coefficient embedding
includes ℓ=2 and E=ℚ_ℓ. No extra qcqs, nonemptiness, derived completeness,
Tor restriction or triangulated field-source hypothesis is added. The full
subcategory uses the ambient morphisms and all three triangle arrows.
There is no statement dispute.

Searches for an existing whole statement:

- msearch.py leanfinder: “Actual integral coefficient extension on pro etale module
  sheaves is exact and its total left derived functor agrees with termwise application
  compatibly with bounded constructible triangles”. Eight hits, including generic Ext,
  mapDerivedCategoryFactors and mapDerivedCategoryFactorsh; none states the actual
  integral map identification and the specified constructible triangle compatibility.
- msearch.py loogle: `"mapDerivedCategory", "IsTriangulated"`. One hit, the existing
  generic Mathlib triangulated instance. It supplies the termwise ingredient only.
- msearch.py grep: `mapDerivedCategory.*IsTriangulated|leftDerivedFunctorIsoMapDerivedCategory`.
  One Mathlib hit at ExactFunctor.lean:104; no whole-item match.
- msearch.py leansearch: “The total left derived extension from continuous integral ell
  adic coefficient module objects to field coefficients is exact and triangulated
  compatibly with the bounded constructible inclusions”. Eight hits: totalLeftDerived,
  IsLeftDerivedFunctor.mk, generic derived triangulatedness and related general APIs;
  no exact actual-coefficient/constructible comparison.
- rg of lean/WeilConjectures and lean/Sheaf for integralScalarExtension,
  padicIntegersToPadicSubfield, boundedConstructibleExtendScalars, comparison and
  continuousIntegers found the dependencies and related localization constructions,
  but no declaration of this node's combined statement. The upstream ID grep had no hit.
  The comparison names introduced here have no existing declaration.


## Returned-delivery repair

The return on immutable head 1f03d3b050c5 identified H13/H2: rebinding Q36's
sk-def-sfb-bounded-constructible record orphaned its owner and affected nine
live importers. That dependency node file is absent. Its module and record
are unchanged. The item's lean.note explains its direct import of the general
ProEtaleBoundedConstructible interface already re-exported by the Q36 owner.

The advisory about integralExtension_sourceTriangulated is handled by using
the cited landed C4 instance directly, with a public import of its module.
The redundant source theorem is no longer restated. Likewise L additivity
uses Mathlib's existing instance for triangulated functors. Neither change
removes a mathematical clause.

The required initial dry run of the retained packet reproduced its 60-second
compile timeout. The failure was repaired in the mathematical module, with
no tool edits, timeout changes or edits to the read-only library. Profiling
isolated repeated concrete graded-tensor elaboration: the explicit derived
functor identification took about 14 seconds, and the typed concrete
termwise comparison about 24 seconds. The two coefficient identifications
were separately confirmed by rfl (43.9/36.0-second sandbox/library checks),
so they do not require duplicate postponed theorem declarations.

The final comparison definition uses the same abstract leftDerivedUnique
constructor as the existing concrete wrapper. It retains the actual L from
the recorded adjunction and its actual leftDerivedFunctorCounit. A named
setup theorem states that counit's universal property. The shift instances
have explicit class types using the cached functor and their unchanged ofIso
bodies. No theorem
is proved and no data are replaced by an unconstrained choice.

Further compile feedback isolated repeated coefficient and module-structure searches.
Named canonical instance caches remove those searches: a diagnostic passed its
sandbox and library checks in 47.4 and 59.9 seconds. Its class-reducibility warnings
were repaired by declaring these as ordinary instance declarations with explicit
types. No warnings are suppressed.

The primary signature is unchanged and verbatim in lean.statement. All
variables and universes are bound; lines are at most 100 characters. The
packet contains exactly one node and its owning module. Against the current
read clone, the node differs only in lean. The delivery wrapper rebases on
current server state and performs the authoritative preflight.

Validation: scompile.py compiled the final owning module cleanly under both
sandbox and actual library names (42.8 and 38.1 seconds), within the unchanged
60-second limit. No warnings or errors remained.

Consumer validation: scompile.py compiled a separate importing scratch module
cleanly under sandbox and library names (5.6 and 5.9 seconds). It checked by
rfl that integralExtensionTermwiseComparison is the original
leftDerivedFunctorIsoMapDerivedCategory, and synthesized both L.Additive and
boundedConstructibleExtendScalars.Additive. Thus the implementation change
retains the canonical map and the original functor instances. The owning
module was independently compiled again in that overlay (42.8/38.1 seconds).
Only the owning module, node and report are delivered; scratch checks are not.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
