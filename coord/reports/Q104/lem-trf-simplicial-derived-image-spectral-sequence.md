## Worker report

Q104 repairs the immutable returned head `52d712dec528`, rather than rebasing an unchanged packet.
The initially retained packet passed the requested first mechanical dry run, but its source-to-Lean
self-check confirmed the maintainer's substantive objections. The module was therefore repaired.
No assertion of independent mathematical acceptance is inferred from that initial dry run.

The delivery module is `Sheaf.TraceFormula.SimplicialDerivedImageSpectralSequence`, namespace
`AlgebraicGeometry`. Its main declaration is `simplicial_derived_image_spectral_sequence`.
All postponed proofs are named theorems with source and complete proof docstrings. Definitions
have explicit data; the only choices used are those already in the published adjunction and
right-derived-functor constructions. All 29 owning declarations are in `lean.declarations`.

The source statement, proof, and proof dependencies are unchanged from the current shared DAG.
The old sandbox `statement_change` described a defect of the old Lean, not of the mathematical
statement, and has been removed. There is no mathematical statement correction and no
`STATEMENT-DISPUTED` flag. The original hypotheses allow arbitrary schemes and arbitrary
commutative constant coefficients; none of properness, hypercover descent, flatness of a map,
Noetherianity, or an upper cohomological bound is imposed.

### Hypotheses and clauses, in source order

1. An augmented simplicial scheme `a : U → X` is represented by
   `X : Scheme.{u}` and `U : SimplicialObject (Over X)`. Its underlying simplicial scheme is
   `U ⋙ Over.forget X`; its degree-p structure map is `(U.obj (op ⦋p⦌)).hom`. A compatible
   family of structure maps is precisely a functor to `Over X`, so this changes no hypothesis.
2. Arbitrary commutative coefficients are `(Λ : Type (u + 1)) [CommRing Λ]`. The module model
   is `Sheaf (totalEtaleTopology U) (ModuleCat.{u+1} Λ)`, named `SimplicialEtaleMod`, and the
   analogous `EtaleMod` on a component. This is the constant-module sheaf encoding already
   used by the landed `totalEtaleAugmentationAdjunction`, not a new ring or category structure.
   The recorded comma-category total site supplies the transition data and degreewise topology.
3. The derived categories are the recorded Mathlib localizations. Explicit
   `HasDerivedCategory.{w}` binders permit any common localization universe. The bounded-below
   category and actual functors are `DerivedCategory.Plus` and `Functor.rightDerivedFunctorPlus`.
   Enough injectives for these sheaf categories is inferred, not added as an extra hypothesis.
4. Exact restriction is `simplicial_etale_restriction_exact`, for every U, Λ, and p. It states
   finite-limit and finite-colimit preservation and injective preservation for the published
   `totalEtaleRestriction` with coefficients `ModuleCat Λ`. The injective clause is also the
   source proof's ingredient needed for the derived component formula.
5. For every simplicial morphism `h : V ⟶ U`, `simplicialEtaleMorphismDirectPresheaf` is a real
   compatible-section construction: right Kan extension along the morphism of comma categories,
   followed by restriction to target étale test objects. `simplicialEtaleMorphismDirect` is its
   sheafification. `simplicial_etale_morphism_direct_image` asserts that the presheaf is already
   a sheaf, gives its inverse-image adjunction and exact inverse image, and identifies both
   inverse/direct restrictions with the ordinary component `Etale.upperStar`/`Etale.lowerStar`.
   Consequently no unconstrained functor can stand for `h_*`.
6. `simplicial_etale_derived_component` identifies the actual `Rh_*` followed by actual derived
   restriction with actual restriction followed by `Rh_p,*`. Its ordinary and derived
   isomorphisms satisfy the explicit `rightDerivedFunctorPlusCompUnit` equation. This is a
   natural isomorphism of functors on all bounded-below complexes, not an objectwise coincidence.
7. Triangulated exactness of `Rh_*` and of the component `Rh_p,*` is asserted in that theorem;
   triangulated exactness of `Ra_*` is the first conjunct of the main theorem. The inverse images
   are exact, so their right adjoints preserve injectives; the docstrings give the resolution
   argument for these exact functors of triangulated categories.
8. `simplicial_etale_direct_image_composition` states both ordinary and derived composition
   for any `W → V → U`, with the derived-unit equation. The companion
   `simplicial_etale_composite_adjunction_normalization` states that the derived comparison is
   exactly `conjugateIsoEquiv` under the composite derived inverse-image adjunctions. It also
   has the ordinary conjugate's unit equation. This schema holds for every specified exact
   inverse adjoint and comparison, so it applies to the inverse adjoints supplied above and
   does not choose an unrelated direct image. Conjugation encodes both unit and counit laws.
9. For a general map of augmented diagrams over `f : Y ⟶ X`, the theorem
   `simplicial_etale_augmented_diagram_comparison` binds the actual commuting equation
   `h.app n ≫ a_U,n = a_V,n ≫ f`. It identifies `Rh_* ⋙ Ra_U,*` with `Ra_V,* ⋙ Rf_*`, together
   with the ordinary square and derived-unit normalization. The companion
   `simplicial_etale_augmented_adjunction_normalization` identifies this construction with the
   conjugate of a specified inverse-image square under the two composite derived adjunctions.
   Its equations use the actual augmentation adjunction and actual étale adjunction. They
   include nonidentity base maps, units, and counits, rather than a tautological component square.
10. The arbitrary cohomological lower bound is `c : ℤ`. `DerivedCohomologicalLower A c` is the
    full subcategory of `DerivedCategory.Plus A` where `IsZero (H^q L)` for every integer q<c.
    The main theorem supplies a `SimplicialAugmentationSpectralSequence` for every c. Thus L and
    its vanishing hypothesis are bound by the functor's source, not replaced by strict termwise
    vanishing of the input complex.
11. `SimplicialAugmentationSpectralSequence.sequence` is a functor from this full derived
    subcategory to Mathlib's `CohomologicalSpectralSequenceNat B 1`. Its first-page natural
    isomorphisms `pageOne p q` identify `(p,q)` with degree `c+q` cohomology of the actual derived
    component direct image. The helper `simplicial_etale_augmentation_component` identifies
    that composite's right derived functor with `Ra_p,*` of the restricted complex, with its
    derived-unit normalization. Hence this is exactly the source's E1 indexed by p≥0, q≥c.
12. `simplicialEtaleCosimplicialPresheaf` is a canonical right Kan extension retaining both the
    degree and structural map to X; its value at `(p,T/X)` is `F(p,U_p ×_X T)`. Sheafifying
    degreewise gives `simplicialEtaleCosimplicialDirect`. The record's `componentIso` identifies
    its evaluations with the actual component direct images. `augmentationCoface` transports
    the actual `SimplexCategory.δ i` maps along these isomorphisms. The `differential` field
    explicitly equates transported d1 with the signed sum of the induced derived coface maps
    after cohomology. There is no existential unconstrained differential and no self-equality.
13. `computation L` supplies a bounded-below injective complex I, zero in degrees j<c, and an
    isomorphism `DerivedCategory.Plus.Q.obj I ≅ L.obj`. It supplies a commuting double complex
    K with `(p,q)` term identified with `(a_p,* I_p^{c+q})`. The horizontal differential is the
    explicit alternating sum of the genuine cosimplicial cofaces. The vertical differential
    is the actual resolution differential under the same term identifications. Column
    cohomology identifies E1 and its d1. The total-differential equation on `ιTotal` is exactly
    `d_face + (-1)^p d_resolution`, using the existing Mathlib total, not a new total convention.
14. Computation is imposed on ALL pages: `computation` gives a decreasing subcomplex filtration
    of `augmentationIntegerTotal K`, whose terms are precisely the sum of the images of the
    columns i≥p. Every page is isomorphic to the actual filtered-complex cycle/boundary
    subquotient `filteredComplexPageObject`, and every differential commutes with the recorded
    `FilteredComplexPageDifferential`. The record identifies total cohomology with actual
    `H^(c+n)(Ra_*L)` and identifies its abutment filtration with the image filtration on that
    same total complex. This excludes an unrelated double complex or filtration.
15. `filtration L n : DecreasingFiltration (H^n(Ra_*L))` binds EVERY integer n.
    `filtration_zero` states F0=top; `filtration_finite` states Fmax(n-c+1,0)=bottom.
    No uniform upper bound occurs. `graded L n p` binds EVERY integer p and identifies its
    graded piece with `augmentationStableTerm (sequence.obj L) c p (n-p)`.
    This term is the actual page at r=p+(q-c)+2 within the half-plane. At that page all further
    incoming and outgoing differentials vanish by their first-quadrant shape. Outside the
    half-plane it is the zero object. It is not an unrelated variable named E-infinity.
16. `sequence` and `pageOne` give functoriality for arbitrary derived morphisms. `filtrationMap`
    and `filtrationMap_comm` put the actual cohomology map on every filtration step;
    `graded_natural` compares its induced cokernel map with `augmentationStableMap` on the
    very same stable pages. These equations imply identity/composition compatibility by
    monicity of filtration arrows and epicity of cokernel projections.

### Dependency declarations used

* `Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite`: `TotalEtaleSite`, `totalEtaleTopology`,
  `totalEtaleRestriction`, and the explicit comma-category model.
* `Sheaf.AlgebraicGeometry.TotalEtaleAugmentationAdjunction`: `totalEtaleToOver`,
  `totalEtaleAugmentationDirect`, `totalEtaleAugmentationInverse`,
  `totalEtaleAugmentationAdjunction`, and their exactness/additivity interfaces.
* `Mathlib.AlgebraicGeometry.Sites.Etale`: `Scheme.smallEtaleTopology`, `Scheme.Etale`;
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: `Etale.upperStar`, `Etale.lowerStar`,
  `Etale.upperStarLowerStarAdjunction`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules` is the recorded general
  ringed-site model; here the constant-module specialization is the `ModuleCat` sheaf model
  used by the landed augmentation node, with Mathlib's existing abelian structure.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`, `HasDerivedCategory`;
  `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` and
  `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction`:
  `rightDerivedFunctorPlus`, `rightDerivedFunctorPlusUnit`, `rightDerivedFunctorPlusCompUnit`,
  `rightDerivedFunctorPlusNatTrans`, `mapDerivedCategoryPlusNatIso`,
  `mapDerivedCategoryPlusCompIso`, and `Adjunction.derivedPlus`.
* `Mathlib.Algebra.Homology.SpectralSequence.Basic`: `SpectralSequence` and its morphisms;
  the nat first-quadrant cohomological specialization and `SpectralSequence.pageFunctor`.
* `Sheaf.CategoryTheory.DoubleComplexTotal`, together with
  `WeilConjectures.Mathlib.Algebra.Homology.TotalComplex`: `HomologicalComplex₂`, its existing
  `total`, `ιTotal`, `ιTotalOrZero`, and the standard first-quadrant signs and total structure.
* `Sheaf.Algebra.Homology.FilteredComplexSubquotients` and
  `Sheaf.CategoryTheory.FilteredComplexPageDifferential`: `DecreasingFiltration.complexStep`,
  `filteredComplexPageObject`, `FilteredComplexPageDifferential`.
  The existing `DecreasingFiltration` and `gradedPiece` are reused, not copied.
* `Mathlib.CategoryTheory.Preadditive.Injective.Basic`: `Injective` and
  `Adjunction.map_injective`; the existing injective-resolution machinery is used.
* `Sheaf.CategoryTheory.Sites.GeometricMorphism`: the recorded `GeometricMorphism` interface;
  composite inverse-image normalization here is spelled out with its underlying composite
  adjunction, so that the derived unit and counit comparison is visible in the signature.

The item gains only three already-landed statement dependencies: the augmentation adjunction,
filtered-complex subquotients, and filtered-complex page differential. No new definition node or
independent theorem node is needed: the additional declarations spell out the original item's
canonical constructions and its already-stated clauses. The modules of recorded proof
dependencies are imported for the subsequent proof; generic leaves are supplied by Mathlib.

### Edge cases

* The indexing is translated by c, not truncated at zero: e.g. c=-2 and total n=-1 has
  contributions from p=0,q=-1 and p=1,q=-2. `graded` includes both.
* For n<c the finite bound is zero; F0 is both top and bottom, forcing the required zero
  abutment. All `graded` pieces are still quantified. At n=c the bound is one and only p=0
  can contribute. For p<0 or q<c, the stable term is explicitly zero.
* At n=0 and c=-2 the finite bound is three, as required; no uniform bound on n is asserted.
* The stable-page index is r=p+(q-c)+2. It exceeds p and (q-c)+1, so the incoming and outgoing
  bidegrees lie outside the first quadrant, including the corner (p,q-c)=(0,0).
* Identity simplicial maps, identity base maps, and composite maps remain allowed; none is
  excluded by the adjunction normalizations. Nonidentity base maps occur explicitly.
* Zero coefficients, the zero complex, constant simplicial schemes, and the empty scheme
  impose no extra nonemptiness, nonzero-ring, properness, or finite-dimensionality assumption.
* The only strict lower bound on a complex appears on the chosen injective representative,
  as a conclusion; input objects need only cohomological vanishing. No upper bound is used.

### Searches and source checks

`msearch.py Q104 lem-trf-simplicial-derived-image-spectral-sequence` was used with:

* `leansearch`: "augmentation spectral sequence of simplicial etale sheaves from a bounded
  below injective resolution". Eight hits were generic injective-resolution constructions
  and simplicial augmentation (`InjectiveResolution.of`, `SimplicialObject.augment`, etc.);
  none is this statement.
* `leanfinder`: "functorial augmentation spectral sequence of simplicial etale module sheaves
  computed by alternating faces of injective resolutions". Eight hits included Dold--Kan,
  normalized Moore complexes, and alternating-face constructions; no exact theorem.
* `loogle`: "CategoryTheory.Functor.rightDerivedFunctorPlusCompIso,
  AlgebraicTopology.alternatingCofaceMapComplex". No hits; the project-specific first name
  is not indexed. This was not treated as proof of absence: the actual project derived
  composition/adjunction source was read and reused instead.
* Mathlib `grep`: "simplicial.*derived.*image|augmentation.*spectral". No exact match.

`rg` in the prescribed upstream `WeilConjectures` and shared `lean/Sheaf` directories found
the generic total-complex spectral sequences and the now-landed total augmentation adjunction.
The existing total-slice-site augmentation spectral sequence concerns a different input and
not the node's arbitrary bounded-below complexes on simplicial schemes. The node-id grep in
upstream did not find an existing statement. Saved `searches.jsonl` retains the search results.

The local Stacks source was read at Tags 0DH0/0DH1, 0D99, and 0D7F, including the injective
alternating-face proof. The actual source and docstrings of the imported canonical interfaces
were inspected. Where the older checkout lacks the current filtration source,
`scompile.py --source WeilConjectures.CategoryTheory.Abelian.Filtration` supplied the live
source; its `DecreasingFiltration` and cokernel `gradedPiece` are the ones used here.

## Second reading by Q104

The dispatcher explicitly forbids starting other agents, so this is a separate second
self-reading, not a claim that an independent worker reviewed this packet. The maintainer's
independent review is still required. I read the original node, repaired module, and Stacks
clauses together and checked the return points separately:

* Arbitrary functors: removed as replacements for derived images. The primary theorem uses
  the published canonical augmentation direct image and concrete canonical component direct
  images; the morphism clauses use the actual compatible-section direct image. Generic record
  parameters are instantiated in the conclusion, never supplied as hypotheses of the result.
* Tautological differential: replaced by an equality with the actual alternating derived
  coface sum. The double-complex equations also identify both actual differentials.
* Unrelated E-infinity: removed; `augmentationStableTerm` is a specified page of `sequence`.
  All pages are tied to the same filtered total complex by page and differential comparisons.
* Excluded negative degrees: removed; n,p,c are integers in the abutment and graded statements,
  and q is translated by c on the natural-indexed pages. The negative and zero-region cases
  were checked above, including n<c and c=-2,n=-1.
* Missing comparisons: supplied actual component and composition natural isomorphisms with
  explicit right-derived-unit and composite-adjunction conjugate equations.
* Missing naturality: supplied the spectral-sequence functor, first-page natural isomorphisms,
  filtration-step maps, stable-page graded naturality, and augmented-diagram comparisons over
  an arbitrary base morphism, including the adjunction normalization of their units/counits.
* Missing double-complex computation: supplied the injective representative, actual cofaces
  and resolution differential, total sign, all-page filtered subquotients and differentials,
  total-to-derived cohomology isomorphisms, and the actual image filtration on that total.

Every top-level declaration has the owning blueprint/source docstring. All variables and
universes are explicit (`autoImplicit false`). The signature recorded in the JSON is extracted
verbatim from the module. No source mathematical statement was weakened to fit an API.

### Validation

The repaired module passed `scompile.py` in both sandbox and library module names with no errors
or non-sorry warnings. The prescribed delivery dry run and final delivery are run after this
report and the node record are finalized.
