## Worker report

States `AlgebraicGeometry.AlgebraicSpace.module_surjectivity_open` in
`Sheaf.AlgebraicGeometry.SpaceModuleSurjectivityOpen`. Its only proof is `sorry`.
No definitions, auxiliary postponed lemmas, dependency repairs, new nodes, or
statement corrections are needed. The original node is unchanged except for `lean`.

Source read: `literature/stacks-project/spaces-flat.tex`, `situation-iso`
(lines 1015ff.) and Tag 09TP, `lemma-F-surj-open` (lines 1696ff.), including
its proof. Its three hypotheses are precisely local finite presentation of f,
finite type of G, and proper support of G. The node spells out the carrier
interpretation of proper support; the Lean uses that interpretation verbatim.

Hypotheses and clauses, matched individually:

- Base scheme and size convention: `{S : Scheme.{u}}`, with explicit `universe u`
  and `set_option autoImplicit false`. The established algebraic-space framework
  uses schemes/sections in u and small-etale site objects in u+1. No equality
  between independent site universes or extra size hypothesis is imposed.
- Algebraic spaces and morphism: `{X B : AlgebraicSpace S}` and `(f : X ⟶ B)`.
  This uses the recorded fppf-sheaf full subcategory; no scheme-only specialization.
- Local finite presentation of f: `(hf : MapIsLocallyOfFinitePresentation f)`.
  There is no global finite-presentation, quasi-compactness, or separation assumption.
- Quasi-coherent modules F and G: `(F G : X.QCoh)`; the actual underlying module
  sheaves are `F.obj` and `G.obj`. The map is `(u : F.obj ⟶ G.obj)`.
- Finite type of G: `(hG : G.obj.IsFiniteType)`, the Mathlib local finite-generation
  predicate. No finite-generation or finite-presentation hypothesis is put on F.
- Proper support: `hproper` introduces `Z : AlgebraicSpace S` and `i : Z ⟶ X`.
  `IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom`
  says i is a closed immersion on every scheme test. `MapIsProper (i ≫ f)`
  says Z is proper over B. `N : Z.Modules`, `N.IsQuasicoherent`, `N.IsFiniteType`,
  and `Nonempty ((moduleDirectImage i).obj N ≅ G.obj)` are the required finite
  type quasi-coherent carrier module and its direct-image identification. This
  is exactly the existential used in `ProperQuotient.properSupport`; that field
  is not itself an independent predicate that could be applied to the present G.
- A test S-scheme and its arbitrary map to B: `∀ (T : Over S)
  (b : yoneda.obj T ⟶ B.obj.obj)`. By Yoneda, this is exactly a scheme T over S
  with an S-map T → B. No condition such as flatness is put on b.
- X_T and its projection: the existing `CostructuredArrow.mk b` is the scheme
  test, and `properQuotFst f (CostructuredArrow.mk b)` is the first projection
  from the actual sheaf fibre product, `properQuotFibre`, to X. Its definition
  uses `fibreProduct_isAlgebraicSpace`; no arbitrary pullback model is supplied.
- The arrow u_T is `(moduleTensorPullback (properQuotFst f
  (CostructuredArrow.mk b))).map u`. This is the recorded tensor pullback
  adjoint to the normalized direct image, including its module scalar extension.
- Surjectivity is `Epi` of that module-sheaf arrow: sheaf-local surjectivity,
  not surjectivity of the map on sections on every open/chart.
- The representing open is `∃ V : OpenSubspace B`. This is the recorded open
  subfunctor with inclusion representable by open immersions, hence the open
  subspace of B, rather than an unrelated open subset or abstract representing type.
- For every T and b, the conclusion is the equivalence between surjectivity and
  `∃! v : yoneda.obj T ⟶ V.val.toFunctor, v ≫ V.val.ι = b`.
  This specifies the canonical representing bijections completely. The map
  Hom_S(T,V) → V_u(T) sends v to its composite with the fixed inclusion.
  It is injective because a subfunctor inclusion is monic, and surjective by
  the displayed criterion. Under T' → T it is precomposition on both sides,
  so the bijections and their inverses are natural. Thus the formula gives the
  requested natural identification, including its map to B, without merely
  asserting existence of arbitrary equipotences. It also includes arbitrary
  nonflat base changes.
- Finite presentation and relative flatness in the node's introductory conventions
  do not assert that F or G has either property. Accordingly there is no such
  extra hypothesis. The recorded flatness module is nevertheless publicly imported
  as the statement-dependency contract requires.

Dependency declarations read and used:

| Node / module | Declaration or role |
| --- | --- |
| def-pc-scheme / Mathlib.AlgebraicGeometry.Scheme | AlgebraicGeometry.Scheme; Scheme.Hom |
| def-weil-size-convention | recorded metatheoretic convention, explicit u |
| def-trf-algebraic-space / Sheaf.AlgebraicGeometry.AlgebraicSpace | AlgebraicSpace, Modules, IsRepresentableWith, structureSheaf |
| lem-trf-space-fibre-products-etale-covers / Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers | fibreProduct_isAlgebraicSpace, used in properQuotFibre |
| def-trf-space-quasi-coherent-module / Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule | QCoh, using Mathlib SheafOfModules.IsQuasicoherent |
| def-trf-space-etale-module-functors / Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations | moduleDirectImage, moduleTensorPullback, moduleTensorAdjunction; normalized chart-limit construction |
| def-pc-scheme-module-flat-over / WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic | Scheme.Modules.IsFlatOver; convention only, no flatness assumed |
| def-sfb-space-proper-quot-functor / Sheaf.AlgebraicGeometry.SpaceProperQuotFunctor | ProperQuotTest, properQuotFibre, properQuotFst; ProperQuotient.properSupport supplies the carrier formula |
| def-sfb-space-morphism-properties / Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties | MapIsLocallyOfFinitePresentation, MapIsProper |
| def-a1-space-open-subspace / Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace | OpenSubspace |

All statement dependency modules are public imports. Already stated proof dependencies
are plain imports: `Mathlib.CategoryTheory.Adjunction.Limits`
(`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`),
`Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus` (`point_open_calculus`),
`Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient` (`space_invariant_open_quotient`),
`Sheaf.AlgebraicGeometry.ReducedClosedSubspaceSupport`
(`exists_unique_reduced_closed_subspace`),
`Sheaf.AlgebraicGeometry.SpaceGeometricPointsConservative`
(`geometricStalk_mono_epi_iso_iff` and the stalk comparisons), and
`Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests`
(`openSubspace_factor_schemeTests`). The module docstring carries every proof step.
`lem-sfb-space-qcoh-kernels-colimits` and
`lem-sfb-space-finite-type-support-pullback` have no recorded Lean module or Mathlib
match on the read base, so there is no stated proof dependency module to import
for those two. Neither is needed to type the present statement. No import cycle
was encountered.

Edge cases checked before writing:

- G = 0: u_T is always surjective; the criterion allows the whole open B.
- F = 0 with nonzero G: surjectivity holds exactly where the pulled G vanishes;
  the statement does not accidentally require finite presentation of G.
- Empty T: the unique empty-scheme factor exists and the pulled arrow is epi.
- Empty B or X and empty fibres: no nonemptiness assumptions exclude them.
- Nonflat closed-immersion base changes are included in the unrestricted b binder.
- Arbitrary characteristic and the existing universe-polymorphic algebraic-space
  size convention are retained.

Searches actually run with msearch.py for this item:

- LeanSearch: `surjectivity locus of a map of quasi coherent sheaves with finite
  type proper support is open`. Eight hits include
  `AlgebraicGeometry.Scheme.Hom.support_ker`, basic-open localization surjectivity,
  stalk-surjectivity facts, and sheaf local-surjectivity facts. None states the
  universal algebraic-space module-surjectivity open locus.
- LeanFinder: `Surjectivity of a homomorphism of quasi coherent modules with finite
  type target and proper support is represented by an open subspace of the base`.
  Eight hits include `AlgebraicGeometry.surjective_isZariskiLocalAtTarget`,
  `Scheme.Hom.app_surjective`, and `PresheafOfModules.IsLocallySurjective`.
  These are scheme morphism/section surjectivity or definitions, not this theorem.
- Loogle: `"SheafOfModules", "surjective"`. Twelve hits include
  `PresheafOfModules.epi_iff_surjective` and
  `PresheafOfModules.IsLocallySurjective`; none gives the open locus result.
- msearch grep: `surjectiv.*(open|proper)|[Ss]urjectivity` in AlgebraicGeometry.
  Twenty reported hits concern ordinary scheme morphism surjectivity, etale/flat
  descent and localizations, not the algebraic-space module result.
- Direct rg on both `lean/WeilConjectures` and `lean/Sheaf` for
  `surjectiv.*(open|proper)|[Ss]urjectivity`, followed by the narrower
  `lemma-F-surj-open|surjectivity_open|surjectivityOpen|surjectivity.*proper support|[Ss]urjectivity locus`.
  The latter only found an affine ideal-generator cover and a constructible-sheaf
  argument, neither matching this theorem.
- Direct grep of `lem-sfb-space-module-surjectivity-open` in
  `lean/WeilConjectures`: no hits. Direct rg of `surjectivityOpen|module_surjectivity_open`
  in `dag/lean_names_upstream.json`: no hits. No declaration is restated.

Validation: scompile.py compiled the module in sandbox mode (9.4 s) and library
module mode (9.3 s), with no errors or warnings. Delivery dry-run and final push
are run through deliver2.py. No disputed statement or node fault was found.

## Second reading by Q02

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
