## Worker report

The module `Sheaf.Paper.GeometricFieldProEtaleEvaluation` states this node as six
named theorems with `sorry` proofs, with explicit canonical helper constructions.
It does not prove the results. The primary declaration is
`AlgebraicGeometry.ProEtale.geometric_field_proetale_evaluation`; the remaining
statement declarations are its `_exact`, `_extension`, `_coherence`, `_identity`,
and `_operations` companions. Every declaration belongs to this same DAG node and
is recorded in `lean.declarations`.

Hypotheses and clauses, matched individually:

- The size convention is explicit `universe u v`: schemes and profinite spaces use
  `u`; set, abelian, ring and module sections use `u+1`. No equality of site object
  and morphism universes is imposed. General coefficient coherence helpers use
  `D : Type v`, `Category.{u+1} D`, the colimits and sheafification needed to form
  the actual inverse-image functor. These specialize to all the coefficient
  categories asserted in the node, without additional mathematical hypotheses.
- The algebraically closed field is `(K : Type u) [Field K] [IsAlgClosed K]`.
  The scheme `Z` is exactly `Spec (.of K)` throughout.
- The specified functor `S ↦ Z[S]` is the existing `profiniteToProEtOf Z`.
  `geometricFieldRestriction` is literally `sheafPushforwardContinuous` for that
  functor, and hence sends F to `S ↦ F(Z[S])`, including the original restriction
  maps. Its topology is exactly `coherentTopology Profinite`, the finite jointly
  surjective topology, and its other site is `Scheme.ProEt.topology Z`.
- Identification of sheaf categories is `IsEquivalence` of that actual restriction
  for sets, abelian groups and rings. `geometricFieldModuleRestriction` is the
  existing `SheafOfModules.pushforward` for the same functor and identity scalar
  map; its equivalence states the compatible identification for an arbitrary ring
  sheaf, including noncommutative rings.
- The specified `p_Z^*` is `profinitePointSetSchemeInverseImage Z` for sets and
  `upperStarFromPoint Z` for abelian groups. `geometricFieldPointAdjunction` and
  `geometricFieldAbelianPointAdjunction` compose the published adjunctions and have
  the actual restriction as right adjoint. Isomorphy of both units and counits
  says that the specified inverse image becomes the identity under restriction;
  no unrelated inverse equivalence is selected.
- Evaluation at Z versus the singleton is `IsIso (geometricFieldTestFinalMap Z)`.
  This is the structural map from the specified singleton test object to
  `Scheme.ProEt.mk (𝟙 Z)`. Applying any sheaf contravariantly yields precisely the
  evaluation identification. The first clause of `_coherence` states its
  compatibility with the evaluation and restriction extension comparisons.
- Every covering admits a section through a member: `_exact` quantifies over
  **presieves**, with `Sieve.generate S` covering, and produces an original member
  `f` with `S f` and a section `s` satisfying `s ≫ f = 𝟙 _`. It does not merely
  select an arrow in the generated sieve.
- Exact abelian evaluation is preservation of finite limits and finite colimits
  by `sheafSections` at `op (Scheme.ProEt.mk (𝟙 Z))`.
- For any `R : Sheaf ... RingCat.{u+1}`, module evaluation is Mathlib's
  `SheafOfModules.evaluation.{u+1} R` at that same object, whose target is precisely
  `ModuleCat (R.obj.obj (op (Scheme.ProEt.mk (𝟙 Z))))`. Preservation of parallel-pair
  colimits renders cokernel preservation (the functor is additive); preservation
  of the discrete `Fin n` diagram of `SheafOfModules.unit R` renders finite free
  module preservation with its canonical coproduct comparison. Evaluation of
  `unit R` is the regular module R(Z) by the existing sectionwise construction.
- An arbitrary algebraically closed extension is `(K K' : Type u)` with the two
  field/closedness instances and **any** `i : K →+* K'`. No algebraicity or
  finite-dimensional hypothesis is imposed. The morphism is exactly
  `Spec.map (CommRingCat.ofHom i)`.
- The inverse image is the recorded `Scheme.proEtaleSheafInverseImage`.
  `geometricFieldRestrictionComparison` applies its adjunction unit, then the
  canonical fibre-product composition isomorphism `geometricFieldTestBaseChange`.
  `_extension` asserts this map is an isomorphism for sets, abelian groups and
  rings: hence scheme inverse image becomes the identity in the profinite-site
  coordinates, with a specified map rather than arbitrary `Nonempty` data.
- `geometricFieldEvaluationComparison` uses the same unit at the final object
  followed by the fibre-product projection `Y ×[Y] X ≅ X`. `_extension` asserts
  it is invertible for sets, abelian groups and rings.
- Composition is the two explicit equations in `_coherence`, through the
  adjunction-conjugate `geometricFieldInverseImageComp`; `_identity` gives both
  identity equations through `geometricFieldInverseImageIdentity`. Composites are
  written as actual composite scheme maps, so no extra algebra-tower structures
  or selected equality transports are imposed on the fields.
- Ring and module operation compatibility is rendered by `_operations`: finite
  product preservation of the actual set inverse image, naturality at an
  arbitrary finite-arity operation, and the equations at every product projection.
  These equations include ring operations and the action `R × M → M`; the empty
  product includes nullary operations. Thus after identifying coefficients, the
  evaluation comparison respects the transported module action. At the level of
  RingCat its components are already ring homomorphisms. Module restriction
  itself uses the identity ring map, preserving the original action sectionwise.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (polynomial splitting,
  equivalent to existence of roots); the algebraic-closure dependency is a
  Mathlib node and needs no replacement declaration.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`,
  and `Spec`.
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`: the recorded
  `Scheme.proEtaleDerivedCategory` fixes the actual `Scheme.ProEt` topology and
  module universe; the derived abbreviation itself is not needed here.
- `Sheaf.Paper.ProfiniteTestObjectFunctor`: `profinite_test_object_functor` and
  its existing underlying `profiniteToProEtOf` from the published ModuleObject
  framework. Its complete finite-limit, finite-cover and limit-presentation
  signature and docstring were read.
- `Sheaf.Paper.ProfinitePointPullback`: the actual
  `profinitePointSetSchemeInverseImage`, `profinitePointSetInverseImage`,
  `profinite_point_pullback`, and the `upperStarFromPoint` framework it exports.
  The recorded declaration family also supplies its ring/module coherence.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafAdjunction`; the exact signatures and
  construction docstrings were read, including the small-model module transport.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` transparently
  denotes the actual `SheafOfModules` used here; its generic-site signature and
  docstring were read. Evaluation and pushforward are Mathlib constructions.
- The proof-dependency imports recorded on this node are included when stated.
  Remaining proof dependencies have no recorded module and cannot yet be imported.

Edge cases checked: empty profinite space gives the empty scheme and is not
confused with the singleton; the empty covering presieve cannot cover a field
spectrum (the split-cover assertion excludes it). Rank zero is included by
`Fin 0`. Arbitrary and zero ring sheaves are included; no nontriviality or
commutativity is imposed on R. Identity extensions and arbitrary transcendental
algebraically closed extensions are included. Empty finite operation arity is
included. No assertion of conservativity of singleton evaluation is made: the
counterexample in Example 4.2.11 remains possible.

Searches (before writing):

- `msearch.py ... leanfinder` with “Sheaves on the proetale site of an algebraically
  closed field are condensed sets and evaluation is exact”: eight condensed-sheaf
  hits, including `Condensed.ofSheafForgetProfinite` and
  `Condensed.isSheafProfinite`; none identifies scheme pro-etale sheaves.
- `msearch.py ... loogle 'Functor.IsEquivalence, SheafOfModules.evaluation'`:
  zero hits (Loogle did not recognize that unqualified identifier).
- `msearch.py ... grep 'IsAlgClosed|geometricField' AlgebraicGeometry/Sites`:
  zero Mathlib hits.
- `rg` of the project upstream ProEtale tree for `IsAlgClosed|geometricField`:
  `AlgClosedFieldSite.lean` supplies split final covering sieves and exactness
  of sections only; `Derived/AlgClosedField.lean` supplies the projective unit
  consequence. Neither states the profinite-site equivalence and its extension
  comparison/coherence. Their full signatures and docstrings were read.
- `rg` for the item id in upstream WeilConjectures: no exact match.
- `rg` of `lean/Sheaf` for `IsAlgClosed|geometricField` and of the relative
  profinite modules for equivalence: no existing declaration of this node.
- Read the actual published 51-module framework in this clone and
  `coord/pefw-upstream-framework.md`; no private replacement of its constructions.
- Read the PDF text of Examples 4.1.10 and 4.2.11 directly. The latter explicitly
  illustrates nonconservative final-object evaluation; the statement avoids it.

No new nodes, dependency record repairs or statement correction were needed.
The initial import of the old upstream global-sections API caused duplicate
pro-etale declaration names against the published FiniteCoefficient framework.
That import was removed; the final-object comparison uses the actual existing
fibre-product projection directly. This changes no mathematical object.

Validation: single-file compilation through the authorized `scompile.py` wrapper
and the `deliver2.py --no-push` dry run; final results are recorded after completion.

## Second reading by ND

Independent reading against the node's unchanged statement and eight proof steps,
Bhatt--Scholze Examples 4.1.10 and 4.2.11 (PDF text read directly), and Stacks
`sites-modules.tex`, `lemma-abelian-abelian` (03CN), and `sites.tex`,
`definition-sheaves-injective-surjective` (00WM). The Stacks assertions assume
only a site. Example 4.2.11 assumes an algebraically closed field; Example
4.1.10 describes the profinite basis and coverings with a finite surjective
subfamily. Neither imposes a characteristic or finiteness restriction here.

Objects, hypotheses and conclusion clauses, in the order of the node:

1. Size convention: explicit `universe u v`, `Scheme.{u}`, `Profinite.{u}`,
   and section categories `Type (u + 1)`, `Ab.{u + 1}`, `RingCat.{u + 1}`.
   The auxiliary coefficient category `D : Type v` has morphisms in `u+1`,
   colimits and weak sheafification precisely to construct the recorded inverse
   image. These are available for the three claimed coefficient categories.
   No equality between site object and morphism universes is assumed. PASS.
2. Algebraically closed field K and Z = Spec K: the binders
   `(K : Type u) [Field K] [IsAlgClosed K]` and every occurrence of
   `Spec (.of K)` give exactly these objects. Read Mathlib `IsAlgClosed` and
   `Scheme`/`Scheme.Hom`, and the algebraic-closure dependency's match. PASS.
3. Functor S to Z[S]: `geometricFieldRestriction` is the actual
   `sheafPushforwardContinuous` along `profiniteToProEtOf Z`, with topology
   `coherentTopology Profinite` and `Scheme.ProEt.topology Z`. Read the
   `profinite_test_object_functor` dependency, including finite-set and limit
   comparisons, and the published ModuleObject.Basic construction:
   `profiniteToProEtOf` is `profiniteToProEt` followed by base change to Z,
   with `profiniteToProEt` built from Spec LC(S,Z). Thus sections and maps are
   restriction along the stipulated functor, not just an abstract equivalence.
   The first three conjuncts of `geometric_field_proetale_evaluation` state
   its equivalence for sets, abelian groups and rings. PASS.
4. Specified p_Z^* becomes identity: read the point dependency's
   `profinitePointSetSchemeInverseImage`, `profinitePointSetInverseImage`,
   `upperStarFromPoint`, and point and scheme adjunctions. The two helpers
   `geometricFieldPointAdjunction` and `geometricFieldAbelianPointAdjunction`
   compose those adjunctions. The main theorem asserts their actual units and
   counits are invertible. Hence the specified p_Z^*, under restriction, has
   the canonical identity comparison. No arbitrary inverse is selected. PASS.
5. Evaluation at Z becomes singleton evaluation: `geometricFieldTestFinalMap`
   is the structural arrow from the singleton relative test object to
   `Scheme.ProEt.mk (𝟙 Z)`. Its `IsIso` conjunct identifies these evaluations
   contravariantly; the first equation of `_coherence` relates it to the
   extension comparisons. The singleton is `ULift PUnit`, not the empty
   profinite space. PASS.
6. Every covering of Z splits through a member: first conjunct of `_exact`
   quantifies over any `Presieve` whose generated sieve is covering and gives
   `U`, an original arrow `f` with `S f`, and `s` with `s ≫ f = 𝟙 _`.
   This is stronger than merely selecting an arrow of the generated sieve
   exactly to the extent required by the node's phrase "through one member".
   It imposes no bound on the number of original covering members. PASS.
7. Exact abelian evaluation: `_exact` states both `PreservesFiniteLimits`
   and `PreservesFiniteColimits` for `sheafSections` at the final object,
   the categorical rendering of exactness in these abelian categories. PASS.
8. Modules over any ring sheaf R: read `ringedSiteModules`, its Mathlib
   `SheafOfModules` definition, and `SheafOfModules.evaluation` and `unit`.
   `_exact` quantifies over all `R : Sheaf ... RingCat.{u+1}`. The evaluation
   target is definitionally `ModuleCat (R.obj.obj (op (ProEt.mk (𝟙 Z))))`,
   the required R(Z)-modules. `PreservesColimitsOfShape WalkingParallelPair`
   supplies cokernels (evaluation is additive). Preservation of the colimit
   of the finite discrete family of copies of `unit R` supplies finite free
   modules and their canonical coproduct comparison; `unit` evaluates to
   the regular module by its construction. PASS.
9. Arbitrary algebraically closed extension: `_extension` has two fields,
   both algebraically closed, and any `i : K →+* K'`. Field maps are
   injective automatically; no algebraicity or finite-generation assumption
   is added. The scheme arrow is `Spec.map (CommRingCat.ofHom i)`. PASS.
10. Scheme inverse image becomes identity under the identifications:
    `geometricFieldRestrictionComparison` is the recorded
    `Scheme.proEtaleSheafAdjunction` unit followed by restriction along the
    explicit `geometricFieldTestBaseChange`. Read the inverse-image
    dependency's base change, direct image, sheafified Kan extension and
    adjunction declarations. `_extension` makes this natural comparison
    invertible for sets, abelian groups and rings. PASS.
11. Canonical evaluation preservation: `geometricFieldEvaluationComparison`
    uses that same unit and the canonical pullback projection over the final
    object. Its three `IsIso` assertions in `_extension` give exactly the
    evaluation comparisons. No unrelated isomorphism is substituted. PASS.
12. Composition and identities: the last two equations of `_coherence`
    compare successive field-extension maps with their actual composite,
    using `geometricFieldInverseImageComp`, the conjugate of the canonical
    direct-image fibre-product comparison. `_identity` uses the analogous
    conjugate identity comparison. The inverse in the composition equation
    has the correct direction from iterated inverse image to composite
    inverse image. No extra chosen tower structure is required. PASS.
13. Ring and module compatibility: the ring comparisons already have ring
    homomorphism components. `geometricFieldModuleRestriction` uses the same
    site functor and the identity map on the restricted ring; its main-theorem
    equivalence therefore retains the action sectionwise. `_operations`
    quantifies over every finite family of underlying set sheaves, every
    operation from its product, and all projections. Its naturality equations
    and finite-product preservation specify preservation of transported
    addition, zero, multiplication, one and R-times-M action, including
    mixed sorts. Together with the singleton equation this gives evaluation
    compatibility with these operations, hence module linearity over the
    transported ring. No restriction to constant or commutative rings. PASS.

Edge cases: all characteristics are allowed. `Fin 0` supplies rank zero;
`I` may be empty in `_operations`, covering nullary operations. Empty
profinite spaces remain allowed among test objects. The empty scheme is
not an omitted base case: Z is the spectrum of a field and hence nonempty.
The empty presieve cannot satisfy the covering premise, as the split-cover
conclusion correctly entails. The zero ring sheaf and zero modules are
included; no `Nontrivial R` appears. Identity and transcendental field
extensions are included. The two fields share the scheme size bound; any
pair can be placed in a common larger universe, as the node's size convention
requires. No conservativity of final-object evaluation is stated; this
agrees with the nonzero quotient of Example 4.2.11 having zero final sections.

Independent searches (different wording from the author):

- LeanFinder: "Restriction of sheaves from a geometric point pro etale site
  to profinite spaces is an equivalence" returned eight condensed/LightProfinite
  hits. `Condensed.ofSheafForgetProfinite` concerns the CompHaus/profinite
  comparison, and the LightProfinite hits concern its diagram model; none
  states a scheme pro-etale equivalence.
- Loogle: `"sheafSections", "IsAlgClosed"` returned no hits.
- LeanSearch: "Sheaves on the pro etale site of an algebraically closed field
  equal sheaves on profinite sets" was unavailable (Internal Server Error),
  recorded by msearch.py; no mathematical inference from that failure.
- `rg` in Mathlib's AlgebraicGeometry/Sites, upstream WeilConjectures,
  the published framework and this project's Sheaf modules for `IsAlgClosed`,
  `Profinite`, `IsEquivalence` and condensed/proetale combinations. Read the
  full `SixFunctors/ProEtale/AlgClosedFieldSite.lean`: its split-sieve and
  surjectivity/epimorphism preservation declarations cover part of this node,
  but neither restriction equivalence nor its prescribed extension/coherence
  comparisons. The derived algebraically closed field file likewise does
  not state the full node. No exact existing declaration replaces this module.

No new definition nodes, dependency modules, statement changes or signature
repairs were needed. All helpers contain real canonical data; all six theorem
bodies remain `sorry`. Every declaration has the source and blueprint docstring,
and the theorem docstrings distribute the node's eight proof steps across the
six statements. Checked the declaration list, explicit binders and universes,
and verbatim equality of `lean.statement` with the main signature. No Lean
source was changed by the second reader: the added material is this independent
review. Authorized scompile.py validation passed for the complete module,
including its sandbox precheck, with no errors or warnings.
