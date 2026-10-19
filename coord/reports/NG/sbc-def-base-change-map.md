## Worker report

Existing declaration: `AlgebraicGeometry.Etale.derivedBaseChangeMap`, in
`WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`, read in the source checkout.
No new Lean module is written: this would duplicate the unbounded exchange already
recorded on `def-kun-unbounded-exchange`. The degreewise presentation already exists as
`AlgebraicGeometry.Etale.baseChangeHomologyMap` in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`.

### Hypotheses and clauses

* Fixed commutative ring: specialize the coefficient category `A` to
  `ModuleCat.{u + 1} Λ`, with `Λ : Type (u + 1)` and `[CommRing Λ]`.
  The categorical, Grothendieck, monoidal closed, symmetric and functorial flat-resolution
  instances are supplied for this category; these are not additional ring hypotheses.
  The size convention is precisely `Scheme.{u}` and sheaves with these coefficients.
* Schemes and arrows: the source declaration's `(X', X, Y', Y)` become `(Y, T, X, S)`;
  its `(g', f', f, g)` become `(e, h, g, f)`. Thus use `CommSq e h g f`, the exchanged
  square. The input is the symmetry of `sq.toCommSq` for the node's
  `sq : ChosenCartesianSquare h e f g`. A chosen Cartesian identification is retained
  in this input datum; the map only needs its commutativity, exactly as the node says.
* Domain and codomain: `R((g)_*[A]) ⋙ L((f)^*[A]) ⟶
  L((e)^*[A]) ⋙ R((h)_*[A])` in diagrammatic functor order. Its component at
  `K : DerivedCategory (Sheaf T.smallEtaleTopology A)` is exactly
  `Lf^* Rg_* K ⟶ Rh_* Le^* K`. There is no boundedness hypothesis.
* Inverse image and direct image are the existing `Etale.upperStar A u` and
  `Etale.lowerStar A u`. The generic `leftDerivedFunctor` and `rightDerivedFunctor`
  are used, rather than introducing new derived operations. The canonical exact-functor
  identification is `Etale.leftDerivedUpperStarIsoMapDerivedCategory` in
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar`; total right derivation is
  the K-injective construction. Its bounded presentation is `rightDerivedFunctorPlus`.
* The inverse-image square is `Etale.derivedSquareUpperStarIso A` on the exchanged
  square. It is the composition identification through the diagonal, equivalently the
  descent of the termwise inverse-image comparison under the canonical exact-functor
  identifications. On the original chosen square the underived comparison is precisely
  `ChosenCartesianSquare.baseChangeInverseImageIso A sq`.
* The defining mate is the body of `Etale.derivedBaseChangeSquare`: `mateEquiv` of
  `derivedSquareUpperStarIso.hom` under the two derived adjunctions. The component
  transpose is explicitly the existing theorem
  `Etale.derivedUpperStar_map_derivedBaseChangeMap_app_counit`: with the above arrow
  substitution, `Lh^*(BC K)` followed by the counit at `Le^* K` is
  `theta K` followed by `Le^*` of the counit for `g`.
* The direct-image form, inserting `η_e` and contracting `ε_f`, is the inverse mate
  under the adjunctions for `e` and `f`. Conjugating the inverse-image composition
  comparison gives `Rg_* Re_* ≅ Rf_* Rh_*`. With the node's explicit conjugate
  normalization, iterated mates recover exactly the displayed composite. This is a
  characterization of the existing map, not another definition of it.
* The degree-q definition is the expression
  `(DerivedCategory.homologyFunctor _ q).map
    ((Etale.derivedBaseChangeMap A exchangedSquare).app
      ((DerivedCategory.singleFunctor _ 0).obj F))`.
  Its bounded-below presentation is the existing `Etale.baseChangeHomologyMap Λ sq q F`,
  where here `sq : IsPullback e h g f`. Its source and target functors in `Defs.lean`
  are explicitly `H^q(Lf^* Rg_* F[0])` and `H^q(Rh_* Le^* F[0])`.
  Exactness supplies the identifications with `f^-1 R^q g_* F` and
  `R^q h_* e^-1 F`. No qcqs hypothesis occurs in these definitions (the introductory
  prose mentions qcqs only for the later base-change property).
* For abelian sheaves take `A = AddCommGrpCat.{u + 1}`, the usual category equivalent
  to ℤ-module sheaves. At q = 0, the existing `Etale.baseChangeMap A exchangedSquare`
  is the mate of the sheaf-level comparison followed by `e^-1 ε_g`, exactly the
  node's degree-zero clause. The module version uses `ModuleCat Λ` throughout.
* Naturality is built into the natural transformation. Pasting and identity
  compatibility remain pointers to their own nodes and introduce no hypothesis.

The attachment records the existing definition, not completion of the surrounding
comparison proofs. In particular `DerivedUnbounded.lean` has a TODO for the comparison
with `derivedBaseChangeMapPlus`; that TODO does not define a different exchange map.
`BaseChange.DerivedComparison` proves the bounded mate agrees with
`derivedBaseChangeMapPlus`. The unit-e/counit-f characterization and the unbounded/bounded
identifications require canonical-comparison proofs when used in stage 3; no claim that
these proofs have already been completed is made here. The formula defining the map
already is the node's equivalent inverse-image mate formula.

### Dependency declarations read

The node's recorded interfaces were inspected in their source modules:

* `Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso`:
  `ChosenCartesianSquare.baseChangeInverseImageIso` (and `ChosenCartesianSquare`).
* `Sheaf.AlgebraicGeometry.DerivedCategories`: `Etale.DerivedCategory.torsionCohomology`;
  its module documentation identifies `Etale.DerivedCategoryModule`, `DerivedCategory`,
  `DerivedCategory.Plus`, `DerivedCategory.Bounded`, and `DerivedCategory.homologyFunctor`.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `Etale.lowerStar`, `Etale.upperStarLowerStarAdjunction`.
* `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`:
  `AlgebraicGeometry.etaleInverseImageModulesExact`.
* `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`:
  `Functor.mapDerivedCategoryPlus` and the unbounded `Functor.mapDerivedCategory`.
* `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: `Functor.exactFunctor_derivedFunctor`.
* `Sheaf.AlgebraicGeometry.KInjectiveResolutions`: `CochainComplex.IsKInjectiveResolution`.
* `Sheaf.AlgebraicGeometry.KInjectiveResolutionsExist`:
  `CochainComplex.etale_kinjective_resolutions_exist`.
* `Sheaf.CategoryTheory.KInjectiveTotalDerived`:
  `CategoryTheory.exists_rightDerived_of_enough_isKInjective`.
* `Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors`:
  `Adjunction.exists_derived_adjunction_of_essentially_constant`.
* `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`:
  `CategoryTheory.ringedToposDerivedPushforwardComposition` (general ringed-site theorem;
  the existing étale functors and their canonical comparisons are used here).
* `WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded`: `Etale.derivedBaseChangeMap`.
* `Mathlib.CategoryTheory.Adjunction.Mates`: `mateEquiv`, `conjugateEquiv`.
* `WeilConjectures.SixFunctors.BaseChange.Derived`: `Etale.derivedBaseChangeMapPlus`.
* `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`:
  `Etale.pullbackSquareComparison`, `Etale.baseChange`.
* `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`: `Functor.homologyFunctorIso`.
* `WeilConjectures.SixFunctors.BaseChange.Square`: `Etale.baseChangeMap`.
* `Sheaf.Paper.KunBcMapOnCohomology`:
  `AlgebraicGeometry.derivedBaseChangeMapPlus_cohomology_resolution`.
* `def-weil-size-convention`: metatheoretic convention, no declaration.
* `Mathlib.CategoryTheory.Adjunction.Basic`: `Adjunction.comp`.
* `Mathlib.CategoryTheory.Localization.Predicate`: `Localization.lift`,
  `liftNatTrans`, `liftNatIso`, `natTrans_ext`.

### Edge cases

There is no nonempty-scheme, nonzero-ring, positive-degree, smoothness, properness,
quasi-compactness or quasi-separatedness assumption in the map. The empty scheme,
zero coefficient ring, zero complex and arbitrary unbounded complexes are allowed.
All integer q are allowed, including negative q (the sheaf-derived higher direct images
then vanish); degree zero gives the underived mate. Identity squares give identity
exchange under the canonical unit identifications. Universes are those already recorded
for module étale sheaves; no separate small test universe is introduced.

### Searches and validation

* `msearch.py ... leanfinder "Derived base change map for etale sheaves defined as the
  mate of the inverse image square and its degree q cohomology"`: 8 hits, ordinary
  sheaf-module pullback and Kähler differential facts; no full Mathlib match.
* `msearch.py ... loogle "CategoryTheory.mateEquiv"`: 12 hits, including the generic
  mate, its counit/unit identities and conjugation identities; generic infrastructure.
* `msearch.py ... grep "derivedBaseChangeMap|baseChangeHomologyMap"`: 0 Mathlib hits.
* `rg` of `WeilConjectures/SixFunctors` for the same map names found
  `BaseChange/DerivedUnbounded.lean`, `BaseChange/Derived.lean`, and
  `Etale/SmoothBaseChange/Defs.lean`; their full definitions and documentation were read.
* `rg "sbc-def-base-change-map"` in the source found
  `BaseChange/DerivedComparison.lean` and `Etale/SmoothBaseChange/Locality.lean`.
  The former explicitly ties the existing bounded mate to this blueprint node.
* `rg` of `lean/Sheaf/AlgebraicGeometry` and `lean/Sheaf/Paper` found many users of the
  existing exchange and degreewise maps, including `KunBcMapOnCohomology`, but no
  replacement definition was needed. The node itself already lists
  `def-kun-unbounded-exchange` in `blueprint.same_as`.
* Server-only `scompile.py` checked the unbounded map, its square comparison, its
  transpose theorem, the degreewise module map and the underived map: clean, 3.3 s,
  nice 19, two threads, 60 s limit. No local compiler or library build was run.

No statement correction, new node, dependency replacement, or disputed statement.

## Second reading by NG

I independently read the node copy, its blueprint source
`sec-smooth-base-change/sk-def-bc/sbc-def-base-change-map.md`, and the source definitions
in `BaseChange.DerivedUnbounded`, `BaseChange.Square`, `Etale.Derived.UpperLowerStar`,
`Etale.SmoothBaseChange.Defs`, `BaseChange.DerivedComparison`, and
`Etale.BaseChangeTheorems.MorphismDefs`. I also read the Stacks source
`sites-cohomology.tex`, Remark `remark-base-change` (lines 4033–4058), and
`etale-cohomology.tex`, the introduction of `equation-base-change` (lines 18310–18360).
These construct the map for unbounded objects and arbitrary commutative diagrams;
properness, torsion and boundedness enter only the subsequent isomorphism theorem.
The blueprint fixes the Cartesian diagram but assumes none of those properties.

The object/hypothesis/clause inventory, with its Lean rendering and verdict:

1. A fixed commutative coefficient ring Λ: specialize the existing coefficient category
   `A` to `ModuleCat.{u+1} Λ`, with `Λ : Type (u+1)` and `[CommRing Λ]`.
   The server elaborates this specialization for a variable Λ, without any additional
   instance assumption. Thus the generic declaration's categorical, Grothendieck,
   monoidal, closed, sheafification and flat-resolution requirements do not add ring
   hypotheses. Verdict: matches.
2. Four schemes, four edges, and a chosen Cartesian identification: the dependency is
   `ChosenCartesianSquare h e f g`. I read its structure, including `isoPullback`,
   `hom_fst`, `hom_snd` and inherited `CommSq`. The map uses
   `sq.toCommSq.flip : CommSq e h g f`. In the upstream binders this substitutes
   `(X',X,Y',Y)=(Y,T,X,S)` and `(g',f',f,g)=(e,h,g,f)`.
   Only commutativity is used by the construction; restricting an existing construction
   to the chosen Cartesian squares is exactly the definition in the node. Verdict: matches.
3. Module sheaves and derived categories: the recorded `DerivedCategories` module
   explicitly uses `DerivedCategoryModule Λ T = DerivedCategory
   (Sheaf T.smallEtaleTopology (ModuleCat.{u+1} Λ))`. Its bounded subcategories and
   cohomology are `DerivedCategory.Plus`, `DerivedCategory.Bounded` and
   `DerivedCategory.homologyFunctor`. The existing exchange has precisely these
   unbounded categories. Verdict: matches, with no boundedness assumption.
4. Exact inverse image, direct image, and their derived adjunctions: I opened the
   signatures of the dependency declarations, including `upperStar`, `lowerStar`,
   `etaleInverseImageModulesExact`, `mapDerivedCategoryPlus`,
   `exactFunctor_derivedFunctor`, `IsKInjectiveResolution`,
   `etale_kinjective_resolutions_exist`, `exists_rightDerived_of_enough_isKInjective`,
   and `exists_derived_adjunction_of_essentially_constant`.
   Upstream `leftDerivedUpperStarIsoMapDerivedCategory` identifies `L(upperStar)`
   with the functor induced termwise by the exact inverse image;
   `derivedUpperStarLowerStarAdjunction` is the derived underived adjunction.
   `preservesKInjectiveComplexes_lowerStar` and the total right derived functor supply
   the stated K-injective interpretation. Verdict: the same operations, not a different
   module pullback over varying ring sheaves.
5. For every unbounded K on T, a morphism in D(X): the checked component is
   `(Etale.derivedBaseChangeMap (ModuleCat Λ) sq.toCommSq.flip).app K`, of type
   `(R(lowerStar g) ⋙ L(upperStar f)).obj K ⟶
   (L(upperStar e) ⋙ R(lowerStar h)).obj K`. Functor composition is diagrammatic.
   This is exactly `Lf* Rg* K ⟶ Rh* Le* K`. Verdict: matches.
6. The defining composite: `derivedBaseChangeSquare` is the `mateEquiv` of
   `derivedSquareUpperStarIso.hom`, under the adjunctions for g and h after exchanging
   the square. Its transpose is precisely the equality
   `derivedUpperStar_map_derivedBaseChangeMap_app_counit`, which I checked at a
   variable Λ and K. The comparison uses `leftDerivedUpperStarComp`, constructed
   from the underived composition isomorphism and exact-functor derivation. It is
   therefore the descended termwise inverse-image comparison. I read
   `ChosenCartesianSquare.baseChangeInverseImageIso`: its direction is the inverse
   of `squareUpperStarIso` on the original square, hence the direction on the flipped
   square. Verdict: matches the node's equivalent defining inverse-image formula.
7. The unit-e/counit-f presentation: `conjugateEquiv` reverses transformations between
   left adjoints to transformations between right adjoints, and `Adjunction.comp`
   has the node's composite unit and counit. I read these definitions and
   `ringedToposDerivedPushforwardComposition`; the node explicitly normalizes the
   direct-image comparison as the conjugate of the inverse-image comparison.
   Expanding the inverse mate inserts η_e, the conjugate comparison, then ε_f,
   giving the displayed formula. This is equality of the two presentations of the
   same map, not a new arbitrary comparison choice. Verdict: matches. The upstream
   TODO about comparison proofs is not represented as a completed proof here.
8. Degree q and sheaf F: the checked expression is
   `(DerivedCategory.homologyFunctor _ q).map
   ((Etale.derivedBaseChangeMap (ModuleCat Λ) sq.toCommSq.flip).app
   ((DerivedCategory.singleFunctor _ 0).obj F))`.
   This is exactly the node's definition, and needs no new named definition.
   The existing bounded presentation is `Etale.baseChangeHomologyMap Λ sq' q F`
   for `sq' : IsPullback e h g f`. Its body is homology of `Etale.baseChange` at F[0].
   I checked the signatures of `baseChangeSourceFunctor` and `baseChangeTargetFunctor`:
   they have the stated two cohomology objects. The exact pullback comparisons identify
   them with `f⁻¹ R^q g* F` and `R^q h* e⁻¹ F`. Verdict: matches; the bounded/unbounded
   comparison is a comparison proof, not a replacement definition.
9. Abelian sheaves and degree zero: the first report's claim to specialize the
   unbounded declaration directly to `AddCommGrpCat` is incorrect: the server cannot
   synthesize its monoidal structure. Likewise raw ℤ in a fixed arbitrary scheme
   universe does not satisfy the large-universe Grothendieck requirement of this
   generic construction. The correct universe-polymorphic specialization is
   `ModuleCat.{u+1} (ULift.{u+1} ℤ)`, checked successfully on the server. The lifted
   integers are canonically ring-isomorphic to ℤ, and ℤ-modules are canonically
   equivalent to abelian groups (`ModuleCat.forget₂AddCommGroupIsEquivalence`, whose
   source I read). Transport gives the abelian-sheaf interpretation; the category
   is not definitionally `AddCommGrpCat`. This correction is now explicit in the
   attachment note. At q=0 the underived `baseChangeMap` is the mate of the same
   square followed by the counit for g, so its transpose is exactly the node's
   `h⁻¹ f⁻¹ g* F → e⁻¹ g⁻¹ g* F → e⁻¹ F`. I also read the recorded
   `derivedBaseChangeMapPlus_cohomology_resolution` signature: its resolution
   formula applies also at q=0; it does not separately assert the q=0 comparison. Verdict: matches through the specified canonical equivalences; no new
   coefficient structure or substitute object introduced.
10. Naturality, pasting and identity: the construction is a natural transformation;
    the two compatibility lemmas remain pointers as in the node. No extra theorem
    is asserted or proved in this delivery. Verdict: matches.

Edge cases: all schemes may be empty, Λ may be the zero ring or have any
characteristic, K may be zero or unbounded in either direction, and F may be zero.
The degree is an arbitrary integer, including zero and negative integers. There is
no index-set/nonemptiness assumption, no smoothness, properness, qcqs or torsion
assumption on the map. The scheme/coefficients universe convention is explicit;
small rings such as ℤ must be lifted to the coefficient universe in a fixed-universe
specialization. No universe or variable is left implicit in the scratch probe.

Independent searches: LeanFinder for "exchange morphism between derived pullback and
derived pushforward for sheaves defined by Beck Chevalley mates" returned eight
ordinary module-sheaf pullback/adjunction hits, not another derived exchange.
Loogle for `CategoryTheory.conjugateEquiv` returned the conjugation infrastructure.
The Mathlib grep search for `squareUpperStarIso|pullbackSquareComparison` returned no
hits. Direct `rg` on the project and upstream with these comparison names and
`exchange|Beck|mateEquiv` found the existing square and derived-exchange modules,
plus users and comparison statements, not a reason to define a second map.

Changes: retained the existing attachment and all node mathematics. Corrected the
`lean.statement` text to include the source's `noncomputable` keyword verbatim;
corrected the attachment note's unbounded abelian specialization and recorded
`CommSq.flip`. The original worker report remains above; this reading supersedes
its direct `AddCommGrpCat` claim and explains the necessary integer-ring universe
lift. No statement correction, new node or dependency module was needed. H5/H6/H8/H9
introduce no new obligations on a statement module because none is delivered: all
map data is the existing construction, with no new proof or hollow definition.

Validation: `scompile.py NG sbc-def-base-change-map
scratchpad/SecondReadingChecks.lean` passed with no errors or warnings, checking the
variable-ring component, flipped comparison, transpose equality, chosen-square
comparison, degree-q expression, existing degreewise interface, underived mate, and
lifted-integer specialization. The script compiled the two required side dependency
modules separately in its private overlay (1.5 s and 1.4 s), then the scratch probe
(3.5 s), each nice 19, two threads, with the 60-second limit. Earlier probe failures
exposed exactly the `symm`/`flip`, monoidal and integer-universe issues described
above and were repaired. No local compiler, global build or upstream edit was used.
