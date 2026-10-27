## Worker report

The module Sheaf.AlgebraicGeometry.NativeAdicMayerVietorisTriangle states
AlgebraicGeometry.ProEtale.nativeAdic_mayerVietoris_triangle with sorry, and defines four
canonical arrow helpers with real data. It states the triangle itself in the unbounded
derived category, not a cohomology-only consequence or a finiteness implication.
The item statement, statement dependencies, proof and proof dependencies are unchanged.
The live node's Q32/L review is its stage-1 proof split; it has no Lean declaration record.
There is no released repair note for this item. The previous stale-dispatch diagnosis
confused the finished stage-1 split with the still-needed stage-2 statement.

Hypothesis and clause correspondence:

- The prime ell is `l : ℕ` with `[Fact l.Prime]`.
- The fixed algebraic closure Omega with extended absolute-value topology is the upstream
  `PadicAlgCl l`, the canonical chosen algebraic closure of `Padic l`, already equipped
  with its extended norm topology. Fixing this representative implements the statement's
  fixed algebraic closure, just as in the source named by the node. It does not replace
  the topology by the discrete topology or by the completion.
- Every scheme T and the target S are `X Y : Scheme.{u}`. The site in `AdicSheaf l X`
  is precisely `Scheme.ProEt.topology X`, on the weakly-etale over-category `X.ProEt`.
  Its universe lift of coefficients is upstream's size convention; `u` is arbitrary.
- The displayed B_T is upstream `adicConstantSheaf l X`, whose sections are
  `ULift (PadicAlgCl.locallyFiniteFunctions l P.left)`. The latter is the subalgebra of
  continuous functions for which every point has a neighbourhood on which the span of
  the values over `Padic l` is finite-dimensional. Ring operations are pointwise and
  restrictions precompose. `AdicSheaf l X` is its internal module category, the existing
  native presentation of these module sheaves; no new module category is defined here.
- Ordinary direct image with its induced scalar action is `adicLowerStar l f` for the
  unrestricted `f : X ⟶ Y`. Its definition uses `modRight` and
  `adicConstantSheafToLowerStar`, the precomposition map. Its total unbounded right
  derived functor is `.rightDerivedFunctor`. This is the upstream universal derived
  functor, with the same right-derived universal property as the recorded generalized
  `rightDerivedFunctorOfQuasiIsoResolutions`; Grothendieck module categories have the
  stronger monomorphic K-injective resolutions required by the upstream construction.
- The two opens are arbitrary open immersions `jU : U ⟶ X` and `jV : V ⟶ X`.
  `_hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base` says they cover X.
  `_hcov` is a real mathematical condition; its underscore is only the unused-binder
  convention for a theorem with a postponed proof.
- `W`, `pU`, `pV`, and `hsq : IsPullback pU pV jU jV` present the intersection.
  `[IsOpenImmersion pU]` and `[IsOpenImmersion pV]` express the open overlap inclusions;
  these properties follow from the pullback and the two open immersions and do not
  restrict which overlap is permitted. Using an arbitrary pullback presentation also
  covers the chosen intersection, without requiring a chosen pullback instance.
- Restriction C|U is `(adicUpperStar l jU).mapDerivedCategory.obj C`, and likewise for V.
  The overlap is the iterated restriction along jU and pU. Exactness makes this the
  termwise derived restriction required by the node. `adicDerivedOverlapIso` identifies
  restriction via V and pV with this same object using `hsq.w` and the canonical
  composition isomorphisms; it is not an arbitrary chosen identification.
- The input `C : DerivedCategory (AdicSheaf l X)` is arbitrary: no constructibility,
  cohomological bound, quasi-coherence, quasi-compactness or Noetherian assumption.
- `adicDerivedOpenRestriction l f j C` derives the ordinary unit followed by the
  composition comparison, using `Functor.rightDerivedPullback`. This comparison is
  normalized on K-injective representatives, so the arrow is the canonical restriction
  induced by the open adjunction unit, not an unspecified arrow between the objects.
- The first arrow `adicMayerVietorisFirst` is `biprod.lift` of the U and V restrictions.
  Its target is the requested direct sum of the two derived images.
- The second arrow `adicMayerVietorisSecond` is `biprod.desc` of the U restriction and
  the negative of the V restriction, with the canonical direct-image congruence and
  overlap comparison. In particular the sign is U minus V. Parentheses in scheme
  composition are normalized using Category.assoc in a proof inside its definition.
- The target of that arrow is R(f jW)_* C|W with jW=pU jU. The conclusion existentially
  quantifies its boundary `δ` into `(Rf_* C)⟦1⟧` and requires exactly the triangle made
  from the two specified arrows and δ to belong to `distTriang` of the target derived
  category. No boundary uniqueness or functorial cone is asserted.

Dependency declarations read and used:

- Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure: AlgebraicClosure and IsAlgClosure;
  the source's fixed model is Mathlib.NumberTheory.Padics.Complex.PadicAlgCl.
- Sheaf.NumberTheory.Padics.CoefficientExtensionFinite:
  Padic.finite_coefficientExtensionRing and its imported coefficient-extension
  constructions, the recorded coefficient-node module.
- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme and Scheme.Hom.
- Mathlib.AlgebraicGeometry.Sites.Proetale: Scheme.ProEt and Scheme.ProEt.topology.
- Sheaf.CategoryTheory.RingedSiteModules: CategoryTheory.ringedSiteModules, the recorded
  general presentation. Its underlying sectionwise module notion is realized natively
  by the existing AdicSheaf module-object construction in the source; no private copy.
- Mathlib.Algebra.Homology.DerivedCategory.Basic: DerivedCategory, HasDerivedCategory.
- Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions: the recorded generalized
  right-derived functor and its unit/universal property. The actual native functors use
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs:
  CategoryTheory.Functor.rightDerivedFunctor, the already-existing total derived functor.
- Mathlib.AlgebraicGeometry.OpenImmersion: AlgebraicGeometry.IsOpenImmersion.
- Mathlib.CategoryTheory.Triangulated.Pretriangulated: Pretriangulated and distTriang;
  the derived category already carries its canonical triangulated structure.

The canonical-map constructions use the source declarations in
WeilConjectures.SixFunctors.ProEtale.Adic.Module: AdicSheaf, adicLowerStar, adicUpperStar,
adicUpperStarLowerStarAdjunction, adicLowerStarComp, adicLowerStarCongr and
adicUpperStarCompIso. They also use Functor.rightDerivedPullback from the upstream
RightDerivedFunctor.ShortExactPullback module and the existing mapDerivedCategoryCompIso,
mapDerivedCategoryNatIso and rightDerivedFunctorNatIso. All helpers belong to this item's
specified canonical triangle, are listed in lean.declarations, have source/blueprint
docstrings and introduce no independent mathematical notion needing another DAG node.

Recorded proof dependencies are imported where stated: ProEtaleWeaklyEtaleLocalization,
RingedSiteRestrictionKFlat, RingedSiteKInjectiveResolutionsOfUniverses,
KInjectiveRestrictLocalized, RingedSiteInjectiveMonoRestriction, KInjectiveTotalDerived
(through the recorded right-derived module), RightDerivedFunctor.Comp, and the Mathlib
DerivedCategory.ShortExact module. The remaining Mathlib weak-etale/open-base-change and
K-injective Hom inputs are in the native imported closure. The theorem docstring gives
all eight steps of the node's proof, merging only its last two map-normalization steps
into the corresponding explicit calculations.

Edge cases checked mathematically before writing the statement: X empty; U or V empty;
U=V=X; disjoint opens; C=0; f the identity; arbitrary non-quasi-compact f; and unbounded
complexes. For U=V=X the first arrow is diagonal and the second is (1,-1). With one open
empty the triangle is the identity with a zero term. For disjoint opens the overlap
vanishes. The chosen coefficient sheaf vanishes on the empty object by the empty-cover
sheaf condition. No edge case forces finiteness or a cohomological bound.

Searches performed:

- msearch leanfinder, query "Mayer Vietoris distinguished triangle for derived direct
  images of adic sheaves": eight generic GrothendieckTopology.MayerVietorisSquare hits,
  including shortComplex, shortComplex_exact and shortComplex_shortExact. These do not
  state the native unbounded derived direct-image triangle with its two maps.
- msearch loogle, query "CategoryTheory.Triangle, DerivedCategory": zero hits, with
  unknown identifier CategoryTheory.Triangle. This failed identifier resolution is not
  evidence of absence; the declaration and its typing were inspected in source and
  checked by compilation instead.
- msearch grep, query "mayerVietoris.*triangle|mayerVietoris.*distinguished": zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id, Mayer-Vietoris triangles,
  native adic names and locally finite continuous functions. The source LowerStar theorem
  is a bounded-constructibility consequence and MayerVietoris.isIso_Q_map_unit_of_isZero
  a supported-object consequence; neither is the requested triangle. The Sheaf structure-
  sheaf and perfect-Hom triangles concern different categories. No exact existing match.
- Read ConstantSheaf.locallyFiniteFunctions, Ring, Module, BaseChange, MayerVietoris and
  LowerStar and the derived functor/adjunction/composition source to verify the actual
  native coefficients, restrictions, ordinary images and canonical comparisons.

Validation: the delivered module passed scompile.py on the live server in both sandbox
and library module mode, within the per-file limit and with no reported errors or
unexpected warnings. autoImplicit is explicitly false and every universe is bound.
No theorem proof was filled. No statement correction, new node or dependency repair was
needed. The independent maintainer review remains the review of this direct delivery.

## Second reading by Q113

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
