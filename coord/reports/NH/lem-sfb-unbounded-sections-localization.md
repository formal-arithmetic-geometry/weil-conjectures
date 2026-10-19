## Worker report

The module `Sheaf.CategoryTheory.Sites.UnboundedSectionsLocalization` states
`CategoryTheory.UnboundedSectionsLocalization.unboundedSectionsLocalization` with `sorry`.
It supplies real helper data for the evaluation functor, termwise restriction, literal
section-complex identity, and the two total right derived functors. No mathematical proof
is supplied: the helper instances apply already existing theorems. In particular, the
identity is `Iso.refl _`, rather than an unspecified isomorphism chosen from existence.

Hypothesis and clause correspondence:

- The small ringed site in a common universe is `{C : Type u} [SmallCategory C]`,
  `{J : GrothendieckTopology C}`, `(R : Sheaf J RingCat.{u})`. Site objects, arrows,
  coefficient values, and module sections all lie in the common universe `u`.
  Grothendieck topologies are the existing sieve encoding of the site coverings;
  no final object of C, pullbacks of C, scheme structure, or commutativity is imposed.
  This is the node's explicit common-universe hypothesis, not a restriction to the
  independent smaller arrow universe of a particular geometric site: such a site
  embeds cumulatively into this common universe. The derived Hom universes `w` and
  `z` are independent of `u` and of each other.
- `ringedSiteModules.{u} R` is the recorded module-sheaf category. The helper
  `modulesGrothendieck` applies the already landed arbitrary-ring theorem
  `SheafOfModules.isGrothendieckAbelianOfUniverses`, with all its size parameters
  specialized to the specified common universe. Its K-injective resolutions are
  then the existing Grothendieck/K-injective instances. The item gains that theorem's
  node as a statement dependency; this does not add a mathematical hypothesis.
- `W : C` is the arbitrary site object. The localized topology, ring and restriction
  are exactly `J.over W`, `R.over W`, and `SheafOfModules.overFunctor R W` of the
  dependency record. `Over.mk (𝟙 W)` is the slice's final object.
- `evaluation R W` is `SheafOfModules.forget R` followed by presheaf-module
  evaluation at `op W`, followed by `forget₂ (ModuleCat _) AddCommGrpCat`.
  Thus it retains the coefficient action up to the specified forgetting step.
  Deriving the composite is canonically equivalent to deriving module evaluation
  and then forgetting, because the latter forgetful functor is exact.
- All complexes are `CochainComplex ... ℤ`; all derived categories are Mathlib's
  full `DerivedCategory`, with no bounded-below or bounded predicates. The
  `HasDerivedCategory` binders choose localization models, not assumptions about K.
  `derivedEvaluation` is the existing `Functor.rightDerivedFunctor`, computed on
  K-injectives. `derivedRestriction` is the same total right derivation of the exact
  localized restriction, hence is canonically the usual derived restriction `j_W^*`.
  Its displayed definition is an actual functor, not a bare object assignment.
- `∃ e : derivedEvaluation R W ≅ derivedRestriction R W ⋙ ...` is the isomorphism
  of functors to `D(Ab)`. Naturality in every derived morphism is part of `NatIso`.
- The first conjunct quantifies over EVERY K-injective complex I. Its equation
  compares `e` at `Q.obj I` with the standard `rightDerivedFunctorObjQIso` for
  restriction and both evaluations. The right side is the standard computation
  isomorphism followed by `Q.map (sectionComplexIdentity R W I).hom`.
  `sectionComplexIdentity` is literally `Iso.refl _`, including differentials.
  The restricted complex is K-injective by `isKInjective_restrict_localized`, via
  the existing zero-preservation theorem; this is not an additional hypothesis.
  The normalization determines the natural isomorphism uniquely, since every
  derived object has a K-injective representative. For any representative of a
  given K, naturality transports exactly this same comparison along its representing
  isomorphism; it is not limited to the chosen representative of the localization.
- The second conjunct quantifies over arbitrary derived K and every `q : ℤ` and
  states `Nonempty` of the isomorphism between the two values of
  `DerivedCategory.homologyFunctor AddCommGrpCat q`. The witness is obtained by
  mapping `e.app K` through that functor. Negative, zero and positive degrees are
  all included. There is no boundedness hypothesis anywhere.

Dependency declarations read and used:

- `def-weil-pbc-sites-and-cohomology`: module
  `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`;
  this module also imports Mathlib's existing site/sheaf interface. We use its
  Grothendieck-topology/sheaf encoding and do not require a new coverage choice.
- `def-weil-size-convention`: metatheoretic convention, with explicit `u w z` here.
- `def-weil-sheaf-of-modules-category`: module
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`.
- `def-pur-localized-ringed-site`: Mathlib module
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`,
  `SheafOfModules.overFunctor`, together with `GrothendieckTopology.over` and
  `Sheaf.over`. The actual sectionwise construction is used throughout.
- `sk-def-sfb-derived-categories`: no record existed; see Dependency modules below.
  The concrete total derived functor and its normalization are from
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective`.
- `lem-pur-kinjective-restrict-localized`: module
  `Sheaf.Algebra.Homology.KInjectiveRestrictLocalized`,
  `CategoryTheory.isKInjective_restrict_localized`, with its exact full signature.
- `lem-weil-pbc-kinjective-hom-derived`: Mathlib
  `CochainComplex.IsKInjective.Qh_map_bijective`,
  `DerivedCategory.Plus.Qh_map_bijective_of_isKInjective`, and
  `CochainComplex.IsKInjective.quasiIso_iff`; these are the recorded Mathlib match.
- `prop-pur-kinjective-resolutions-exist`: module
  `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`,
  `SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses`.
  It is imported as a proof dependency. For an arbitrary ring sheaf the existing
  `lem-weil-pbc-ring-sheaves-grothendieck` interface supplies the needed resolution
  instances without requiring a commutative-ring lift.
- Existing helper interfaces: `module_overFunctor_preservesZero` from
  `Sheaf.Algebra.Homology.RhomIntoKInjectiveLocal`, and
  `localized_restriction_adjunction` from
  `Sheaf.Algebra.Homology.LocalizedRestrictionAdjunction`. The latter supplies
  additivity as part of its already established adjunction interface.

Edge cases checked against Stacks sites-cohomology.tex, lines 4314--4346:
K=0 gives the identity on the zero evaluated complex; W final reduces to the
usual global-section calculation; arbitrary W needs no terminal object of C;
negative q and complexes unbounded in both directions remain present. Empty C
has no W and therefore no instance of the statement. The zero ring and zero
module category do not invalidate any functor or identity. No assumption that
forgetting a K-injective module complex makes it K-injective as an abelian
sheaf complex is made: evaluation is derived in the module category.

Searches for an existing declaration (2026-10-18):

- `msearch.py ... leanfinder "Unbounded derived sections of module sheaves agree
  with derived sections of the localized slice site"`: eight hits, on local
  generators and unrelated localization; no matching theorem.
- `msearch.py ... loogle "SheafOfModules.overFunctor"`: three hits, giving exactly
  the existing restriction, its composition comparison, and the scheme over
  equivalence. These are used, not copied.
- `msearch.py ... grep "rightDerived|overFunctor"
  Algebra/Category/ModuleCat/Sheaf`: five hits, all in PushforwardContinuous,
  with no unbounded comparison theorem.
- `msearch.py ... leansearch "total right derived functor of an additive functor
  on the unbounded derived category computed by K injective resolutions"`:
  eight hits, including totalRightDerived and ordinary rightDerived, but no
  localized unbounded sections comparison.
- `rg` in the named upstream `WeilConjectures` tree for derived evaluation,
  derived sections and rightDerivedFunctor, and for the exact item id: generic
  right-derived APIs and geometric specializations, no match to this theorem.
- `rg` in `lean/Sheaf`: CohomologyOverObjectLocalization is for abelian sheaves
  and natural-number cohomology of sheaves, not arbitrary unbounded module
  complexes. RGammaDerivedLimit supplies commutative-ring derived sections,
  not this comparison or its normalization; its type does not cover arbitrary
  RingCat coefficients. RingedSiteDerivedRestriction is an object assignment
  on chosen representatives, not the natural comparison here. No exact match.

Validation: scompile.py compiled the delivered module both under its sandbox
name and under its library module name, cleanly, in about 3 seconds each.
Only the main theorem has a postponed proof. No statement correction or dispute.

## Dependency modules

`sk-def-sfb-derived-categories`: its record was null, although the unit is a
collection of existing conventions. Under §1(B) the delivery records the existing
interfaces rather than introducing another derived category. The primary record
is the already landed `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`
from `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: its source,
full variable context and universal/computation docstrings were read. It takes
arbitrary quasi-isomorphic K-injective resolutions, exactly the unit's generic
hypothesis, unlike the older upstream monomorphic-resolution typeclass. On the
Grothendieck categories in this item the upstream rightDerivedFunctor is the same
universal functor up to its unique unit-compatible isomorphism and supplies the
explicit `ObjQIso` normalization used here. The item imports both interfaces.

The other conventions are already encoded by Mathlib `DerivedCategory`,
`DerivedCategory.Plus`, and `CochainComplex.IsKInjective`; the already recorded
left-derivation interfaces `leftDerivedFunctorFromTotalTensor` and
`leftDerivedFunctorFromTotalTensorIsoMapDerivedCategory`; and the existing derived
adjunction construction. The category table uses DerivedCategory instantiated
on the recorded sheaf/module-object categories, not another construction.
The full `AlgebraicGeometry.ProEtale.BoundedConstructible` definition and docstring
were read in the 51-module framework at the specified shared path: it is the full
subcategory of objects bounded for the canonical t-structure and with every
cohomology object satisfying IsConstructibleModuleObject. Its predicate uses the
existing arbitrary-matrix local finite presentations, not constant-scalar ones.
No boundedness or constructibility predicate is imposed on this item's K.
Only this dependency's `lean` field changes. No dependency statement is altered,
no new theorem or module for the convention is needed, and no existing object is
redefined. The note records each component's source module explicitly.

## Second reading by NH

The dispatcher instructs this worker to deliver directly and prohibits additional
agents; the independent reader is the maintainer after delivery. This section
records the worker's own second pass, not an independent review.

Reopened the node and completed module. All hypotheses and clauses match as above:
common-universe small site and ring, arbitrary W, localized sectionwise restriction,
unbounded total right derivation, natural D(Ab) isomorphism, literal identity on
every K-injective representative, and all integer cohomology groups. In this pass
I checked especially that restrictedKInjective uses the existing Tag 08FI theorem,
that the normalization contains the actual Q of the identity, and that the two
rightDerivedFunctorObjQIso factors land in that exact restricted complex. The
compiler's definitional equality check accepts Iso.refl for the section-complex
identity. No mathematical clause was changed. The only dependency-record repair
is the absent convention binding described above. Initial elaboration faults were
repaired by explicit imports for privately imported dependency declarations and
by expanding evaluation to its existing additive functor composition; the final
compilation has no errors or warnings.

Dry-run repair: the existing-declaration probe imports the primary module alone.
I removed cross-module names from lean.declarations; their exact existing modules
remain documented in lean.note and this report. The list now contains only names
exported by the primary module. No mathematical statement changed.

Preflight repair: removed the unsupported convention metadata key from the
dependency lean record and aligned its signature with the existing node/source
convention (the signature begins at def). The common-universe Grothendieck theorem
is intentionally a statement dependency because its instance is needed to type
the actual derived functor definitions; adding an already landed node is
expressly authorized by the stage-2 brief.
