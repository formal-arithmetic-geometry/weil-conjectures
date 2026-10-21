## Worker report

The module `Sheaf.Paper.FiniteCoefficientModelComparison` states
`AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteCoefficientModelComparison`.
Its only postponed proof is that theorem, with `sorry`. The conclusion is an existing,
normalized `Encoding A X` together with the proposition-valued record
`FiniteCoefficientModelComparison A X e`, which spells out all the comparison clauses.
The record and the four auxiliary predicates have complete definitions, not postponed data.
No new nodes, dependency repairs, or statement correction are needed.

Source read: the second paragraph of
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-prop-integral-criterion/sk-prop-integral-criterion-reductions.proof.md`,
including its reference to classical finite-stalk constructibility; and
`sk-def-sfb-constructible/_section.md`, clauses 1, 2, and the final paragraph.
The seven-step proof of this node is reproduced in the theorem docstring.

Hypothesis and clause correspondence:

* A Noetherian scheme X: `(X : Scheme.{u}) [IsNoetherian X]`.
* A finite commutative ring A with its discrete condensed structure:
  `(A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]`,
  `[Finite A] [DiscreteTopology A]`, and the existing `coefficient A`. These are the
  existing coefficient-interface binders, not a new ring or extra topological condition:
  a discrete commutative ring is a topological ring.
* The small pro-etale site: all sheaf and module types use `Scheme.ProEt.topology`.
  Schemes lie in universe u, site objects in u+1 and morphisms in u, with coefficient
  modules and stalks in u+1. No equality between object and morphism universes is imposed.
* The identification of `p_X^* underline A` with the constant ring sheaf:
  the existing `Encoding A X` fixes `ringIso` and its constant-section normalization;
  its `ordinary_functor` is exactly the section-action functor followed by restriction
  of scalars along that ring isomorphism. It is not an arbitrary equivalence.
* Internal modules and ordinary module sheaves: the theorem uses the existing
  `Internal A X` and `Ordinary A X`, and the ordinary image is always
  `e.ordinary.functor.obj M`. `Ordinary A X` reduces to the exact intrinsic module category
  expected by the recorded `Scheme.IsConstructibleProEtaleModuleSheaf` declaration.
* Constructibility iff constructibility: the record's `constructible` field compares
  `IsConstantModelConstructible (coefficient A) X M` directly with
  `Scheme.IsConstructibleProEtaleModuleSheaf X A (e.ordinary.functor.obj M)`.
  The existing definitions are used, not replaced by etale origin or locally finite
  presentation over arbitrary local functions.
* The same finite constructible locally closed stratifications: `strata` quantifies
  over every existing `Scheme.Stratification X` and compares the two local conditions
  on each of its actual `domain i` and `immersion i`. Constructibility and local closedness
  are fields of this existing stratification structure. The ordinary local condition is
  precisely `IsLocallyConstantProEtaleModuleSheaf` together with finiteness of every actual
  `proEtaleGeometricModuleStalk`. These are the clauses of the recorded ordinary predicate.
* The same finite-model covers: `covers` quantifies over every
  `Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain i)` and compares the recorded
  `HasFiniteConstantLocalModelOnCover` with finite ordinary constant models on that very
  cover. It uses `finiteConstantScalarExtension`, the existing scalar construction,
  and canonical `proEtaleConstantModulePullback`, not arbitrary pullbacks or maps.
* Arbitrary ordinary trivializing covers, with empty objects discarded: `discardEmpty`
  uses the native ordinary local-constancy interface, including **every** index type
  `I : Type (u + 1)`, site-object family `W`, covering arrows `f`, and arbitrary constant
  module values `P`. Its trivialization hypothesis is exactly the localized-site
  expression `.over (W j) ≅ proEtaleConstantModuleSheafOver ... (P j)` from that definition.
  Under the finite-stalk hypothesis it asserts that the subfamily indexed by
  `{j : I // Nonempty (W j).left}` still covers in `ProEt.precoverage`, that each retained
  original `P j` is finite, and that the internal restriction has an actual finitely
  presented scalar model on that very same object. Thus no refinement, replacement
  value, or finiteness assertion on an empty-object value is smuggled into the statement.
* Exactly the same cohomological vanishing intervals: `intervals` states both directions
  for every complex K and every ordered integer interval [a,b], using `IsZero` on each
  homology object outside the interval, and the actual `e.ordinaryDerived.functor`.
* The bounded constructible subcategories: `ordinaryIntrinsicBoundedConstructible` is
  standard t-structure boundedness intersected with the recorded intrinsic ordinary
  constructibility predicate on every homology sheaf. `boundedConstructible` compares
  this to the existing `constantModelBoundedConstructible`. `boundedEquivalence` provides
  an equivalence of these full subcategories and a natural isomorphism making its
  inclusion commute with `e.ordinaryDerived.functor`. This specifies the induced
  equivalence, rather than merely asserting that two unrelated categories are equivalent.
  No Tor-amplitude, completeness, or finite free-model hypothesis appears.

Dependency declarations used (the first five are the original statement dependencies):

* `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, `ProEt.topology`,
  `ProEt.precoverage`, `Scheme.proetalePrecoverage`.
* `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `coefficientRing`, `condensedRingObj`; the existing finite coefficient and internal
  module abbreviations use this precise pullback-from-the-point construction.
* `Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence`:
  `FiniteDiscreteOrdinary.coefficient`, `Internal`, `Ordinary`, `Encoding`,
  `Encoding.ordinaryDerived`, and `moduleObject_ordinary_coefficient_equivalence`.
* `Sheaf.Paper.CondensedConstantConstructibility`:
  `HasFiniteConstantLocalModel`, `IsConstantModelConstructible`,
  `constantModelBoundedConstructible`, `ConstantModelBoundedConstructible`.
* `Sheaf.Paper.ProEtaleConstructibleSheaf`:
  `Scheme.IsConstructibleProEtaleModuleSheaf`, with its exact intrinsic module interface.
* `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`:
  `InternalAbelianSheafModule.sectionModuleEquivalence`.
* `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`:
  `InternalModuleOperations.internal_module_operations_transport`.
* `Mathlib.Algebra.Module.FinitePresentation`: `Module.FinitePresentation`.
* `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`:
  `scalarRingObj`, `finiteConstantScalarExtension`, `HasFiniteConstantLocalModelOnCover`,
  `finiteConstantLocalModel_iff_exists_cover`.
* `Sheaf.Paper.ProEtaleFiniteModelStalks`: `finite_geometricStalk_of_finite_models`.
* `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`:
  `Scheme.proEtaleObjectInverseImageRestriction`.
* `Sheaf.AlgebraicGeometry.ProEtaleInverseImageStalk`:
  `Scheme.proEtaleInverseImage_setStalk`, `proEtaleInverseImage_abelianStalk`.
* `Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk`:
  `Scheme.proEtaleConstantModuleGerm_bijective`.

All recorded proof-dependency modules are imported. Helpers reuse the existing canonical
module pullbacks, constant modules, localized constants, and geometric stalks. The ordinary
bounded helper is in the intrinsic category used by this node: the existing
`ordinaryBoundedConstructible` is instead in the fixed-ModuleCat presentation;
`intrinsicOriginBoundedConstructible` is in a separate transported origin category.
Neither is silently substituted for this node's intrinsic ordinary category.

Edge cases checked:

* A=0 and zero sheaves: no `Nontrivial` hypothesis; finite presentation/finite-set
  equivalence remains valid. A finite nonfield such as Z/4 and its module Z/2 is allowed;
  the models are finitely presented modules, never required to be free or projective.
* Empty schemes, empty strata, and empty covering families: all local conditions can be
  vacuous where appropriate. `strata` is pointwise, even for a zero-stratum partition.
  The recorded ordinary global predicate requires positive stratum count; on the empty
  scheme a single empty stratum meets that convention. Common positive-count
  stratifications supply exactly the same witnesses on both sides.
* Infinite module values on empty covering objects: these are not asserted finite.
  The `discardEmpty` clause removes precisely those objects, retains the covering
  condition, and only then asserts the original values finite.
* Large trivializing families: the native-cover clause uses I in u+1, matching the
  ordinary predicate, rather than restricting that clause to the smaller cover universe
  of the existing internal OnCover predicate.
* Negative degrees, single-degree intervals, arbitrary ordered bounds, unbounded ambient
  derived categories, and bounded constructible complexes of infinite Tor dimension:
  none is excluded. In particular there is no finite-Tor intersection.

Searches actually run with the mandated msearch.py wrapper:

* LeanFinder: "For a finite discrete ring, finite constant local models coincide with
  locally constant finite stalk constructible module sheaves on a Noetherian scheme".
  Eight hits including `CondensedMod.isDiscrete_tfae`,
  `CompHausLike.LocallyConstantModule.functor`, and `Module.isLocallyConstant_rankAtStalk`.
  These do not state this constructibility/witness/derived comparison.
* Loogle: `"constantSheaf"`. Twelve hits including `CategoryTheory.constantSheaf`,
  `constantSheafAdj`, and `instAdditiveSheafConstantSheaf`; infrastructure only.
* LeanSearch: "finite ring constructible sheaf constant models finite stalks derived
  equivalence". Eight hits on `Sheaf.IsConstant`, its essential-image/counit criteria,
  and isomorphism invariance. No match for the item.
* Mathlib grep, subdirectory CategoryTheory/Sites:
  `finite.*constructib|constructib.*finite|constant.*local.*model`: zero hits.
* Project rg on finite constructibility and constant local models in
  `lean/WeilConjectures/ConstructibleSheaf`,
  `lean/WeilConjectures/SixFunctors/ProEtale`, and `lean/Sheaf/Paper` found the recorded
  definitions, finite coefficient and origin interfaces, and other comparisons. None
  gives this finite-model/finite-stalk theorem. The blueprint-id grep in
  `lean/WeilConjectures` found no match. A declaration-name rg in Mathlib CategoryTheory,
  WeilConjectures, and Sheaf found no collisions for any declaration introduced here.
* Inspected `ConstantCoefficientLocalModelsComparison`: it compares two constant module
  constructions on an equal-universe site, not the internal/ordinary constructibility
  and bounded-derived categories in this node. Existing origin/comparison predicates
  were inspected before adding the intrinsic bounded helper.

No `STATEMENT-DISPUTED` issue remains. The item statement and all dependency records are
unchanged. The only node change is its `lean` attachment.

## Second reading by Q03

This is a second pass by the worker, with the node and final module open. The dispatcher
explicitly prohibits starting another agent; the independent maintainer review follows
this delivery, as specified in the task brief.

I checked the Noetherian, finite, commutative, and discrete hypotheses against the theorem's
binders and the existing coefficient encoding. I checked the iff against the two recorded
constructibility definitions, the stratum and covering-object restrictions against their
actual canonical pullbacks, and the induced derived functor against
`Encoding.ordinaryDerived` rather than a separately chosen functor. I checked every
vanishing-degree condition and the natural isomorphism with the full-subcategory inclusions.

The first draft expressed discarding empty objects only for scheme covers with index
universe u. Reading the ordinary local-constancy signature again exposed the missing native
I in u+1 case. The final `discardEmpty` field now quantifies over its exact site-localized
trivialization signature, retains its original values on nonempty objects, asserts the
pruned site family covers, and supplies internal scalar models there. The scalar-model
encoding requires `open scoped CategoryTheory.Obj` for the existing transported ring-object
instance; this scope was added without a local instance or new ring structure.

The positive-number convention in the ordinary definition was checked separately: the
local stratum comparison is pointwise for every stratification; global existence on the
empty scheme is witnessed by one empty stratum. No empty object is required to have a
finite original constant value. All helper definitions contain real expressions and the
single theorem proof remains `sorry`, with the complete seven-step argument in its docstring.
