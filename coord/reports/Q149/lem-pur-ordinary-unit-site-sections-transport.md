## Worker report

Item: `lem-pur-ordinary-unit-site-sections-transport`, group Q149.
Module: `Sheaf.AlgebraicGeometry.OrdinaryUnitSiteSectionsTransport`.
The node is unchanged except for `lean`. No new nodes, dependency repairs,
statement corrections, disputed statements, or additional assumptions are needed.

The module constructs terminal-section direct-image identifications, the associated
canonical Leray isomorphisms, and the ordinary section pullbacks on the two sites.
These are actual compositions of the published adjunctions and derived comparison
constructions, with no chosen unspecified maps. Five named theorems, all with proof
`by sorry`, give the separate clauses of the item. Every declaration is listed in
`lean.declarations` and has a source/blueprint docstring. Every theorem docstring
contains the corresponding natural-language proof. No data is supplied by `sorry`.

Hypotheses and objects, clause by clause:

- The schemes and scheme morphism are `{Y X : Scheme.{u}} (f : Y ⟶ X)`.
  The quasi-compact and quasi-separated hypotheses are the named instances
  `[hqc : QuasiCompact f] [hqs : QuasiSeparated f]`. `include hfinite hqc hqs`
  explicitly retains these assumptions in all five theorem declarations even
  where the equation itself makes sense more generally.
- The finite discrete commutative ring is `Λ : Type (u + 1)` with `[CommRing Λ]`
  and `[hfinite : Finite Λ]`. Fixed-scalar `ModuleCat` sheaves encode discrete
  coefficients and require no auxiliary topology on the carrier of Λ. This is
  exactly the coefficient universe of the recorded mate and global comparison.
- The arbitrary etale sheaf is `L : Sheaf X.smallEtaleTopology
  (ModuleCat.{u + 1} Λ)`; its degree-zero placement is
  `(DerivedCategory.Plus.singleFunctor _ 0).obj L` throughout. L is not assumed
  constructible, locally constant, finite, or perfect.
- The etale and pro-etale derived categories are `DerivedCategory.Plus` of the
  two published fixed-scalar sheaf categories. This is their strictly full D+
  subcategory, sufficient for the node's degree-zero input, its exact pullbacks,
  and right-derived direct images. There is no restriction on the sheaf L.
  The specified intrinsic coefficient category of
  `def-weil-pbc-proetale-modules` is canonically presented by these fixed-scalar
  sheaves through its recorded `finiteCoefficientRealization`; this is the very
  model already used by the dependency's canonical mate and global comparison.
  No alternative coefficient category, completion, or derived functor is created.
- `l` and `r` are `(Etale.upperStar (ModuleCat Λ) f).mapDerivedCategoryPlus`
  and `Etale.rightDerivedLowerStarPlus (ModuleCat Λ) f`, with unit from
  `Etale.derivedUpperStarLowerStarAdjunctionPlus`. `P` and `s` are
  `(ProEtale.upperStar (ModuleCat Λ) f).mapDerivedCategoryPlus` and
  `(ProEtale.lowerStar (ModuleCat Λ) f).rightDerivedFunctorPlus`, with unit
  from `ProEtale.derivedUpperStarLowerStarAdjunctionPlus`. Exact pullback is the
  bounded-below restriction of ordinary derived pullback, with no K-flat choice.
- `C_X` and `C_Y` are the recorded `comparisonUpperStar (ModuleCat Λ)` induced
  on D+. `a` is precisely `fixedComparisonPullbackPlus Λ f`, in the node's
  orientation `C_Y l ≅ P C_X`; `b` is precisely
  `fixedComparisonDirectImageMatePlus Λ f`, with its original normalization.
- `ordinaryUnitSiteTransport` is the displayed unit identity. Lean composes
  left to right, so its right-hand side is `C_X.map eta_e ≫ b.app (l.obj L[0]) ≫
  s.map (a.hom.app L[0])`. The left-hand side is the actual pro-etale adjunction
  unit at `C_X L[0]`, not a newly declared map with those endpoints.
- `ordinaryUnitSiteTransport_isIso` has exactly the additional hypothesis
  `h : IsIso (eta_e.app L[0])`. Its three conjuncts assert invertibility of the
  actual pro-etale unit, the etale ordinary section pullback, and the pro-etale
  ordinary section pullback at `C_X L[0]` respectively.
- Both RΓ functors are `.rightDerivedFunctorPlus` of terminal evaluation:
  `sheafToPresheaf J (ModuleCat Λ) ⋙ (evaluation _ _).obj (op (mk (𝟙 T)))`.
  These are ordinary module-derived global sections. The explicit evaluation
  form also makes their additive instances available without new local instances.
- `ordinaryEtaleTerminalIso` and `ordinaryProEtaleTerminalIso` transport the
  existing direct-image/global-sections identifications through
  `Sheaf.ΓNatIsoSheafSections` at the actual identity objects of the two sites.
  `ordinaryEtaleLeray` and `ordinaryProEtaleLeray` apply the canonical
  `rightDerivedFunctorPlusCompIso'`; its required preservation of injectives
  comes from the existing exact inverse-image adjunction. These are specified
  natural Leray isomorphisms, never arbitrary isomorphisms of the endpoints.
- `ordinaryEtaleSectionUnit` and `ordinaryProEtaleSectionUnit` are evaluation
  of the actual sheaf adjunction unit followed by the terminal comparison.
  Their derived maps `ordinaryEtaleSectionPullback` and
  `ordinaryProEtaleSectionPullback` are
  `rightDerivedFunctorPlusBaseChange` of those natural transformations,
  normalized at the source by the derived identity isomorphism.
- `ordinaryUnitSiteSections_unit_leray` states both unit/Leray formulas,
  including the node's specifically described etale composite
  `RΓ_X.map eta_e ≫ ordinaryEtaleLeray.hom.app (l L[0])`.
  The pro-etale formula uses the corresponding actual pro-etale unit.
- `ordinaryUnitSiteSections_comparison` states the equality of the two
  displayed section maps under `a` and the canonical global comparisons.
  It assumes no invertibility of eta_e. `ordinarySiteGlobalComparison` is
  literally the recorded `finiteComparisonGlobalSections` precomposed with
  `mapDerivedCategoryPlusIdIso.inv` and the functor unitor. The latter source
  transport is needed because the recorded map starts at `RΓ ⋙ D+(𝟭)`, rather
  than syntactically at RΓ. Its arrow and normalization are retained.
- For every integer q the induced cohomology map is the image of the explicitly
  constructed ordinary section pullback under
  `DerivedCategory.Plus.homologyFunctor (ModuleCat Λ) q`. The construction by
  `rightDerivedFunctorPlusBaseChange` is the usual resolution definition of
  pullback: apply the ordinary section-unit map to an injective resolution,
  then a comparison into an injective resolution of the inverse image, and take
  cohomology. Its existing characterization is
  `rightDerivedFunctorPlusBaseChange_fac`; for nonnegative degrees the already
  published `rightDerivedBaseChange_app` identifies this very map with the
  classical derived-functor pullback, using
  `singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso` and
  `mapDerivedCategoryPlusSingleFunctor`. These interfaces are reused, not
  restated as duplicate lemmas. The unit/Leray theorem and the comparison-square
  theorem are equalities in D+, so applying any integer homology functor gives
  their cohomology versions. The negative-degree case is explicit in
  `ordinaryUnitSiteSections_negative`: for `q : ℤ` and `hq : q < 0`, all four
  global cohomology modules in the square are zero, as four `IsZero` conjuncts.
- Naturality is supplied as data: the section units, derived section pullbacks
  and global comparison are `NatTrans`, the terminal and Leray identifications
  are natural isomorphisms, and the units, mate and pullback comparison are the
  dependency's natural transformations. The five statements are at arbitrary L,
  so no arbitrary objectwise isomorphism or non-natural selection is used.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison`:
  `Scheme.proEtaleSiteComparisonModules`, the original-site geometric adjunction.
  The actual fixed-scalar functors are its `ProEtale.comparisonUpperStar` and
  `comparisonAdjunction`, reexported through the imported comparison modules.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`: the recorded
  intrinsic identified-coefficient operations and their canonical adjunction.
  The existing fixed-scalar realization identifies their constant-ring case
  with the `upperStar`/`lowerStar` operations used by the canonical mate. We use
  the latter public API, without separately importing the unrelated ring-sheaf
  construction family or manufacturing an intrinsic replacement.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`: the recorded
  coherent pullback comparison specializes to the canonical comparison. Its
  exact derived specialization used here is the dependency's
  `fixedComparisonPullbackPlus`, defined termwise from
  `comparisonUpperStarCompUpperStarIso`.
- `Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`:
  `fixedComparisonPullbackPlus`, `fixedComparisonDirectImageMatePlus`,
  `isIso_fixedComparisonDirectImageMatePlus`, and
  `fixedComparisonDirectImageMatePlus_counit`. No replacement mate is defined.
- `Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized`:
  `finiteComparisonGlobalSectionsUnit`, `finiteComparisonGlobalSections`, and
  `isIso_finiteComparisonGlobalSections`. The helper only normalizes its source.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`
  supplies the general site convention. The concrete fixed sites, `Sheaf`,
  `sheafToPresheaf`, and `sheafSections` are their existing definitions; no new
  site predicate or cohomology definition is introduced here.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`:
  `Etale.DerivedCategoryModule`, `DerivedCategory.Plus`, homology. The torsion
  predicate is not used or assumed.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`:
  `FiniteCoefficientModules`, `FiniteCoefficientDerivedCategoryPlus`,
  `finiteCoefficientComparison`, and the canonical exact equivalence
  `finiteCoefficientRealization`; this is the recorded fixed-ring/intrinsic
  correspondence, publicly available through the normalized global comparison.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`,
  `lowerStar`, `upperStarLowerStarAdjunction`. Their ordinary D+ versions are
  `mapDerivedCategoryPlus`, `rightDerivedLowerStarPlus`, and
  `derivedUpperStarLowerStarAdjunctionPlus` from the published derived modules.
- The published pro-etale finite-coefficient derived modules supply
  `upperStar`, `lowerStar`, and `derivedUpperStarLowerStarAdjunctionPlus`.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections`:
  `Etale.lowerStarCompGlobalSectionsIso`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.GlobalSections`:
  `ProEtale.globalSectionsLowerStarIso`, `Scheme.ProEt.isTerminalMkId`.
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp`:
  `Functor.rightDerivedFunctorPlusCompIso'`.
- `Mathlib.CategoryTheory.Adjunction.Mates`: `CategoryTheory.mateEquiv`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`: the recorded
  `finiteCoefficientInverseImageMap_isIso` and its constant-section normalization
  are imported as proof dependencies. Their coefficient action is already
  implemented by the fixed-scalar pullback API.
- `lem-pur-site-derived-sections-unit-pasting` currently has no Lean binding.
  It is a proof dependency only, not an object needed to state the item. Its
  node and proof were read; its intended argument is included in the theorem
  docstrings. No missing declaration is assumed in a definition or statement.

Edge cases checked before drafting:

- Λ may be the zero ring; no `Nontrivial` or nonzero-order hypothesis occurs.
  Zero sheaves and their maps are included.
- X or Y may be empty, and f may have empty source. Identity terminal objects
  and the existing sectionwise coefficient identifications remain defined;
  the terminal coefficient sheaf on the empty site has zero sections, exactly
  as in `finiteCoefficientInverseImageMap_empty`.
- f need not be surjective, proper, etale, smooth, or an isomorphism. Its
  only geometric hypotheses in the statements are the node's qcqs ones.
- The identity morphism is included, using the actual canonical adjunctions.
- q = 0 is covered by degree-zero placement and the ordinary section map;
  every negative q has the explicit four vanishing assertions. No positive
  cohomological bound is assumed.
- `Λ : Type (u + 1)` and `Scheme.{u}` match the published small-site size
  convention (object universe u+1, morphism universe u). No equality between
  independent object/morphism universes is imposed.
- The comparison-square and unit/Leray statements do not assume an invertible
  etale unit; that premise is confined to the conditional isomorphism theorem.

Searches for an existing declaration (2026-10-24):

- `msearch.py ... leanfinder "Etale pro etale comparison transports adjunction
  units and ordinary derived global section pullbacks"`: eight hits, headed
  by module-sheaf unit tensor identities and general sheaf adjunction units;
  no exact statement combining the two sites and derived ordinary sections.
- `msearch.py ... leansearch "Derived adjunction units and ordinary global
  sections pullback commute with etale proetale comparison"`: eight hits,
  including `Adjunction.derived_unit` and `derivedη_fac_app`; these are generic
  derived-adjunction formulas and do not give this site-specific statement.
- `msearch.py ... loogle '\"Adjunction\", \"unit\", \"mate\"'`: zero hits.
- `msearch.py ... grep 'globalSectionsUpperStarMap|rightDerivedFunctorCompIso'
  CategoryTheory`: zero hits.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for ordinary unit/section
  transport found canonical mate and normalized global comparison components,
  the pro-etale unit/Leray chain formula in another coefficient presentation,
  and finite ordinary pullback constructions. None states this full node.
- Exact-id search for `lem-pur-ordinary-unit-site-sections-transport` in both
  source trees found no existing declaration. Exact searches for the fourteen
  proposed declaration names found no previous owner in Mathlib or either
  project source tree. `rg` for the relevant global-section definitions led
  to the existing Γ/terminal comparison, Etale global-section pullback and
  derived-base-change APIs reused here.

Source reading: Stacks `proetale.tex`, section `section-comparison` (099R),
and `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/lem-pur-a1-direct-image.proof.md`, Step 4, were read directly.
The node's expanded ordinary-section and adjunction-transpose argument is retained
in the theorem docstrings. The unchanged unit itself is not altered.

## Second reading by Q149

This is the author's second reading of the node and final module, under the
instruction not to spawn other agents; the maintainer supplies independent review.
I checked every hypothesis and clause against the file. The canonical pullback
comparison has the node's `C_Y l → P C_X` orientation. The unit equation uses
`fixedComparisonDirectImageMatePlus` at `l L[0]` and the actual derived unit.
The isomorphism conclusion includes all three named maps. The comparison square
uses the named ordinary maps and the recorded global map, with no extra unit
invertibility hypothesis. Both unit/Leray formulas and all four negative-degree
zero groups are present. Naturality is in the NatTrans/NatIso types.

Two initial interface mismatches were corrected during compilation: the general
chosen terminal object is not definitionally the identity etale object, so the
actual `Scheme.Etale.isTerminalMkId` witness is used; and the recorded global
comparison starts at `RΓ ⋙ D+(𝟭)`, so its canonical source isomorphism is made
explicit in `ordinarySiteGlobalComparison`. Using the evaluation composite also
retains the existing additive instance. No mathematical hypothesis or conclusion
was changed. All variables and universes are explicitly bound with
`autoImplicit false`. No module-local notation or instances are introduced.

## Validation

The final module is compiled with the prescribed `scompile.py`, in module mode,
against the live server's published library. Both sandbox and named-module checks
passed. The only postponed proofs are the five listed theorem declarations.
The prescribed delivery dry run and push are performed after this report is written.
