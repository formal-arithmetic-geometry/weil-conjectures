## Worker report

The module `Sheaf.CategoryTheory.FixedPairCommonDerivedResolution` states
`CategoryTheory.Endofunctor.IsoAlgebra.fixedPair_commonDerivedResolution`, with proof
`sorry`, and gives three real canonical constructions belonging to this node:
`fixedPairForgottenResolutionIso` (a_s), `fixedPairUnderlyingResolutionIso` (b_s), and
`fixedPairCommonModelComparison` (a_s followed by inverse b_s). These are composed from
existing resolution, localization and functor-image isomorphisms; there is no new
choice of an object or map, no hollow definition and no postponed helper theorem.
No node correction, dependency repair or new independent notion is needed.

Hypothesis and clause correspondence:

- C and D are `Type u` and `Type u'`, with independent `Category.{v}` and
  `Category.{v'}`, `Abelian`, and `IsGrothendieckAbelian.{gC/gD}` instances.
  F and H have `Additive` and `IsEquivalence`. Thus the autoequivalences are additive.
- B and E are precisely the recorded `IsoAlgebra F` and `IsoAlgebra H`; their Abelian
  structures are the upstream canonical instances. Their Grothendieck assumptions
  are explicit `IsGrothendieckAbelian.{gB/gE}` binders.
- U_F and U_H are precisely `IsoAlgebra.forget F/H`. Their finite-limit creation,
  exactness and conservativity are explicit `CreatesFiniteLimits`,
  `PreservesFiniteLimits`, `PreservesFiniteColimits`, and `ReflectsIsomorphisms`
  binders. U_F's K-injective preservation is `PreservesKInjectiveComplexes`.
- L has `Additive` and `PreservesFiniteLimits`; `e : L ⋙ H ≅ F ⋙ L` means HL ≅ LF,
  since Lean writes functor composition in application order.
- The existing `mapOfNatIso e` is the functor specified by the formulas: its object
  carrier is `L.obj X.carrier`, its structure is `e.app X.carrier ≪≫ L.mapIso X.str`,
  and its underlying map is `L.map a.hom.f`. The theorem states the structure formula
  and equality `mapOfNatIso e ⋙ forget H = forget F ⋙ L`, which specifies equality on
  all objects and all morphisms. Its first two conjuncts are additivity and left
  exactness of this very functor, rather than existence of an unspecified lift.
- Equality of the two composites of `mapHomologicalComplex (ComplexShape.up ℤ)`
  gives equality on complexes and chain maps, with no boundedness restriction.
  The next conjunct states equality of all `hom i j` components of the two mapped
  homotopies for arbitrary complexes, maps f and g, homotopy h, and integers i,j.
- The existential proof `hB` is exactly `∀ K, ∃ I s, I.IsKInjective ∧ QuasiIso s`.
  The simultaneous proof `hC` supplies this hypothesis for the underlying category,
  as required to instantiate the recorded total right derived functor of L.
  These are proofs of propositions, so their existential binding makes no choice
  of replacement data or extra assumption. All helpers work for any such proofs.
- The universal resolution conjunct states that EVERY `s : K ⟶ I` with
  `I.IsKInjective` and `QuasiIso s` has K-injective forgotten target and
  quasi-isomorphic forgotten arrow. Neither this clause nor the helpers requires
  s to be monomorphic.
- `fixedPairForgottenResolutionIso e hB s` has source
  D(U_H)(R(mapOfNatIso e)(QK)) and target Q(L(U_F I)). Its data is D(U_H) applied to
  the dependency's canonical resolution isomorphism, followed by
  `U_H.mapDerivedCategoryFactors.app (Ltilde I)`.
- `fixedPairUnderlyingResolutionIso hC s` has source RL(D(U_F)(QK)) and the identical
  target Q(L(U_F I)). Its data is RL applied to U_F's exact localization comparison,
  followed by the dependency's canonical resolution isomorphism for U_F(s).
  The dependency `rightDerivedFunctorOfQuasiIsoResolutionsObjIso` is explicitly
  RL(Qs) followed by inverse derived unit at the K-injective target, including the
  quotient-to-Qh identifications. Thus these helpers are precisely the two
  canonical maps in proof step 5, for every resolution s. Their signatures and
  actual constructions supply the resolution-isomorphism clause of the node.
- `fixedPairCommonModelComparison` composes a_s with b_s inverse. This is the
  specified objectwise comparison by the identity on the literal shared target;
  it uses no arbitrary comparison isomorphism.
- The theorem's last two conjuncts quantify over all K-injective I,J and all chain
  maps t. They conjugate D(U_H)R(Ltilde)(Qt), respectively RL(D(U_F)(Qt)), by the
  canonical identity-resolution isomorphisms. Both equal exactly
  `Q.map (L.mapHomologicalComplex.map (U_F.mapHomologicalComplex.map t))`.
  This expresses equality of the actual maps on the common model.

Dependency declarations read and used:

- `def-sp-grothendieck-abelian`: Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic,
  `CategoryTheory.IsGrothendieckAbelian` (the node's Mathlib match).
- `def-weil-endofunctor-fixed-pair-category`:
  WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra,
  `CategoryTheory.Endofunctor.IsoAlgebra`, `IsoAlgebra.forget` and the existing
  `IsoAlgebra.mapOfNatIso`; its carrier, structure and underlying-map formulas were read.
- `def-weil-abstract-derived-category`: Mathlib.Algebra.Homology.DerivedCategory.Basic,
  `DerivedCategory`, `HasDerivedCategory`, `DerivedCategory.Q`, and the Qh comparison.
  The four morphism-size universes wC,wD,wB,wE stay independent. There is no imposed
  equality between category object universes, morphism universes, or derived sizes.
- `def-sfb-right-derived-functor`:
  Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions,
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions` and
  `rightDerivedFunctorOfQuasiIsoResolutionsObjIso`, together with its unit and
  unit-isomorphism theorem used in that construction. This is the recorded interface,
  rather than upstream `rightDerivedFunctor` with its stronger resolution interface.
- Proof dependencies are included: WeilConjectures.CategoryTheory.GrothendieckAbelian.
  KInjectiveResolution (`CochainComplex.kInjectiveResolutionFunctor`,
  `toKInjectiveResolution`, `monoQuasiIso_toKInjectiveResolution_app`,
  `isKInjective_kInjectiveResolutionFunctor_obj`); Mathlib.Algebra.Homology.
  DerivedCategory.ExactFunctor (`Functor.mapDerivedCategoryFactors`);
  Sheaf.CategoryTheory.KInjectiveTotalDerived
  (`CategoryTheory.exists_rightDerived_of_enough_isKInjective`).
- Additional existing interfaces: WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebra
  (transport exactness and forgetful comparison), and
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
  (`Functor.PreservesKInjectiveComplexes`). Finite-limit creation uses Mathlib's
  `CategoryTheory.Limits.CreatesFiniteLimits`.

Edge cases checked before writing: F=H=identity, zero categories and zero complexes,
zero L, left exact but nonexact L (e.g. Hom(Z/2,-) on abelian groups), arbitrary unbounded
complexes, identity resolutions, quasi-isomorphisms that are not monomorphisms,
all positive and negative degrees, and the empty finite diagram. In particular there is
no `PreservesFiniteColimits L` assumption. The common-model construction does not require
L(I) to be K-injective. No statement dispute was found. The proof docstring records
all six DAG proof steps and their dependencies.

Searches for an existing full statement:

- msearch.py leanfinder, query: "A functor intertwining autoequivalences transports
  fixed pairs and its derived values after forgetting have a common K-injective
  resolution model". Eight hits: mapDerivedCategoryFactorsh, mapDerivedCategoryFactors,
  mapDerivedCategorySingleFunctor, two generic localization lifting declarations,
  InjectiveResolution.isoRightDerivedToHomotopyCategoryObj, injectiveResolutions and
  mapHomologicalComplexUpToQuasiIsoFactors. These give ingredients, not this statement.
- msearch.py loogle, query: "CategoryTheory.Functor.mapDerivedCategoryFactors,
  CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIso". Zero hits (IsoAlgebra.mapOfNatIso
  is not indexed by that Mathlib service).
- msearch.py grep, query: "IsoAlgebra|common.*[Rr]esolution|
  rightDerivedFunctorOfQuasiIsoResolutions", subdirectory CategoryTheory. Zero hits.
- rg over live `lean/WeilConjectures` and `lean/Sheaf`, query
  `commonDerivedResolution|common.*[Rr]esolution|mapOfNatIso|
  lem-sf-fixed-pair-common-derived-resolution`: transport is already defined upstream,
  and upstream rightDerivedFunctorMapOfNatIsoCompForgetIso gives a natural comparison,
  but no declaration states this node's canonical common-model and chain-map equations.
  The recorded arbitrary-quasi-isomorphism derived interface is used as required.
- `grep -rn lem-sf-fixed-pair-common-derived-resolution lean/WeilConjectures`: no match.
  Exact-name rg in Mathlib, both library roots and dag/lean_names_upstream.json found
  no collisions with any of this delivery's four declaration names.
- Read the source files named by the node and Stacks local source for Tags 079P,
  070K and 070Y; these agree with the node and the chosen canonical constructions.

Validation: scompile.py compiled the module in sandbox mode and its final library module
name in 2.5 s and 2.4 s respectively, with no errors or non-sorry warnings. An initial
field-notation elaboration failure on the forgotten complex was repaired by using the
fully qualified `CochainComplex.IsKInjective`; no mathematical statement changed.

## Second reading by N6

A second pass over the node and final file checked every correspondence above, in
particular the orientation HL→LF, the order e_X then L(theta_X), arbitrary rather than
monomorphic resolutions, independence of derived universes, and the source/target of
both conjugation equations. The maps are specified using the recorded units and exact
localization comparisons, rather than bare existence of isomorphisms. All data definitions
are real compositions of existing canonical isomorphisms and the only postponed proof
is the main theorem. No mismatch requiring a node change was found. This is a worker
self-check; the maintainer supplies the independent review, as the dispatcher brief
requires and no further agents are authorized.
