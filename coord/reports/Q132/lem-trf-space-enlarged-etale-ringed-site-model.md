## Worker report

The module `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` states the full enlarged
étale ringed-site model. Its main recorded declaration is
`AlgebraicGeometry.AlgebraicSpace.enlargedRestriction_equivalence`; `lean.declarations`
records the constructions and the other clauses. Every theorem has `sorry` as its whole
proof, with source and natural-language proof in its docstring. Definitions have actual
data. No statement correction, disputed statement, independent new notion or dependency
repair was necessary.

I read the node's complete statement, source, statement dependencies and proof. I read
the statement-dependency records and their actual declarations, including the repaired
`AlgebraicSpace` interface, fibre-product and jointly-surjective-family modules, site
covering predicate, ringed-site modules, and Mathlib's localized sheaf/module functors.
I also read the stated proof-dependency modules and the Stacks source at Tags 03G0, 03G1,
03H7, 03G2, 03G8, 03LP, 04LY and 04LZ. The source confirms chartwise étaleness.

Clause-by-clause correspondence:

- Base scheme and algebraic spaces: explicit `S : Scheme.{u}` and
  `X : AlgebraicSpace S`, using the recorded fppf-sheaf full subcategory. Maps are its
  actual natural transformations. All category and coefficient universes are explicitly
  bound. Set sheaves and module carriers live in `Type (max (u + 1) w)`, containing the
  enlarged site's object and arrow universes. The inherited structure ring remains in
  `RingCat.{u}`. No equality of the scheme-site and enlarged-site hom universes is imposed.
- Étaleness: `IsChartwiseEtale f` is precisely the node's quantified test on every
  `T : Over S` and every representable étale `yoneda.obj T ⟶ X.obj.obj`. It does not
  replace chartwise étaleness by the stronger representable predicate `IsEtale`.
- Objects and morphisms of C_X: `EnlargedEtaleSite X` is the full subcategory of `Over X`
  on chartwise étale structure maps, so its arrows are all maps over X.
  `enlargedEtalePrecoverage` uses chartwise étale covering arrows and the existing
  `IsJointlySurjective` on their point classes. Its generated topology is
  `enlargedEtaleTopology`. `enlargedEtale_site` states the covering-site axioms and
  existence of finite limits. The étaleness clause on covering arrows is automatic by
  cancellation between enlarged objects and agrees with the node's covering convention.
- Inclusion of scheme objects: `schemeSpace` uses the actual fppf Yoneda sheaf;
  `schemeSheaf_isAlgebraicSpace` postpones only its algebraic-space property, not its
  underlying presheaf. `enlargedSchemeInclusion` preserves those schemes, their structure
  maps and all scheme arrows. Its continuity is a named theorem.
- Restriction equivalence: `enlargedRestriction` is Mathlib's literal sheaf precomposition
  functor. `enlargedRestriction_equivalence` states that it is an equivalence for sets
  and rings. `enlargedSetEquivalence` and `enlargedRingEquivalence` use `asEquivalence` of
  this exact functor, so their forward functors are the required restriction.
- Extension existence and uniqueness: `enlargedExtension_exists` retains a specified
  restriction isomorphism. `enlargedExtension_unique` quantifies over any two extensions
  and specifies exactly one isomorphism whose restriction induces the identity on F:
  `restriction.map a.hom ≫ d.hom = e.hom`.
- Equalizer formula: `enlargedExtension_equalizer` quantifies over every surjective
  representable étale scheme chart `a`, any scheme overlap `T₁`, and its two projections
  `p q` forming the actual pullback. Its codomain is the literal equalizer subtype
  `{s : F(T₀) // F(p) s = F(q) s}`. The bijection is normalized by the displayed
  restriction-to-the-chart equation. `enlargedChartOverlap_exists` supplies the scheme
  overlap for every such chart. This is independent of presentation: the statement
  quantifies over all pullback presentations. Naturality in both T and F is retained
  by the normalization, not by an arbitrary bijection. For a map of charts or a sheaf
  map, the square of normalized equalizer maps commutes after projection to F(T₀), by
  naturality of G and e; that projection is injective. Thus the normalization equations
  force exactly the natural equalizer identification claimed in the node.
- Structure ring: `enlargedStructureSheaf` is the inverse image of the original
  `structureSheaf` under the ring restriction equivalence;
  `enlargedStructureRestriction` is its specified counit isomorphism. This is the
  permitted construction of an inverse from a categorical equivalence: the theorem
  determines the inverse up to its unique normalized isomorphism. There is no choice
  of unconstrained data from an existence theorem.
- Modules: `enlargedModuleRestriction` is the existing `SheafOfModules.pushforward`
  along the inclusion, using the inverse of the specified structure-ring isomorphism.
  `enlargedModuleRestriction_equivalence` asserts the required equivalence of the
  existing `ringedSiteModules` categories, with no copied module definition.
- Every morphism f: `enlargedFibreProduct` bundles the actual sheaf pullback using
  `fibreProduct_isAlgebraicSpace`. `enlargedBaseChange` takes its first projection and
  uses the canonical pullback map on arrows. `enlargedFibreProduct_chartwise` is its
  named well-definedness obligation. `enlargedBaseChange_continuous` states continuity.
  `enlargedDirectImage` is exactly precomposition by this functor, on objects AND maps.
  `enlargedDirectImage_geometric` states existence of a left exact left adjoint via
  the existing `GeometricMorphism` structure, fixing its direct functor by equality.
  `enlargedSmallDirectImage` is its transport by the two scheme comparison equivalences;
  `enlargedSmallDirectImage_geometric` states the resulting small étale morphism.
- Canonical ringed structure: `enlargedChartLift` is the actual pullback lift of a
  commuting pair of scheme charts. `IsEnlargedStructuralMap` requires pullback of
  regular functions along EVERY such scheme map, including both structure-ring
  restriction isomorphisms. `enlargedStructuralMap_existsUnique` states uniqueness
  with precisely that normalization. `enlargedStructuralMap` chooses this uniquely
  determined map. This states the ring map in the adjoint form
  O_Y → f_* O_X; a genuine RingCat-valued sheaf morphism preserves all ring operations.
  With the geometric adjunction and its left exactness this is precisely the ringed
  morphism f^{-1}O_Y → O_X. If underlying set sheaves are viewed in the larger universe,
  use their common universe lift; precomposition and the ring-map equations commute
  with it. No extra universe restriction or arbitrary structural map is assumed.
- Composition: `enlargedBaseChange_composition` supplies the natural comparison
  W ×_X (X ×_Y V) ≅ W ×_Y V, normalized by BOTH projections, and the exact component
  equality for the composite structural ring maps under this comparison.
  Precomposition supplies the direct-image comparison; its adjunction mate supplies
  the inverse-image comparison. Projection normalization forces their associativity
  coherence. `enlargedBaseChange_identity` separately includes identities, identifying
  the comparison with the second projection and the structural map with its restriction.
- Étale localization: for every `f` with `IsChartwiseEtale f`,
  `enlargedPostcompose` is actual postcomposition and `enlargedLocalization` remembers
  its factorization as an object over `enlargedEtaleObject f hf`.
  `enlargedLocalization_equivalence` states that it is an equivalence and preserves
  exactly the covering sieves. The composite with the slice forgetful functor is
  the displayed postcomposition functor on objects and arrows. Thus restriction
  along it is exactly Mathlib's localized-site sheaf restriction.
  `enlargedEtaleRestriction` is literal precomposition along postcomposition.
  `enlargedEtale_localization` gives its adjunction with the same base-change direct
  image, its left exactness, and the structure-ring identification, normalized to the
  identity of Γ(U,O_U) on EVERY small scheme object. Its final adjunction-unit equation
  identifies the structural ring map with the localization structural map. This
  includes the ringed structure and is stronger information than an unnormalized
  equivalence of the underlying topoi.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `IsSurjective`,
  `EtaleSite`, `etaleTopology`, `structureSheaf`, `IsAlgebraicSpace` and their actual
  sheaf/category interfaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, with `etale_fibreProduct_isScheme` in the proof plan.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`: `IsJointlySurjective`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `ringedSiteModules`; Mathlib's
  `SheafOfModules.pushforward`, `GrothendieckTopology.over`, and `Sheaf.over` supply
  module restriction and the localization convention. No new localization is defined.
- `Sheaf.CategoryTheory.Sites.GeometricMorphism`: `GeometricMorphism`. Its already
  landed node `def-trf-geometric-morphism` is added to stmt_deps as permitted by §5.
- `def-weil-size-convention` has no declaration by its record: explicit universes
  above implement that metatheoretic convention.

All already stated proof-dependency modules are imported without `public`, including
comparison, algebraic-structure transport, site inverse image, composition, ringed
morphisms and the slice presentation. The generic chartwise-permanence proof node has
no recorded declaration, so no nonexistent module is imported. The chartwise definition
and the elementary well-definedness facts here implement the constructions of this
item itself; they do not replace a recorded dependency. The old representable-only
`etaleMap` is not applicable to a general chartwise étale morphism: the local helper
`chartwiseEtaleMap` simply applies the exact chartwise condition to each scheme object.

Edge cases checked before writing:

- Empty algebraic spaces and empty schemes are allowed, with no Nonempty hypotheses.
  Empty covers give singleton section sets, as the equalizer/sheaf condition requires.
- Every surjective étale chart is quantified over, including charts of the empty
  space, and every scheme presentation of the overlap is allowed.
- Arbitrary morphisms f, including nonrepresentable maps, are permitted. Only the
  localization clauses require chartwise étaleness. It is not replaced by representability.
- The identity map and arbitrary composable pairs are explicitly included; no
  affine, separated, quasi-compact, Noetherian, characteristic or coefficient-ring
  hypothesis is added.
- Sheaves and module carriers may be larger than the site; w is arbitrary, with
  max (u+1) w providing the required lower size bound. No equal hom-universe assumption
  is needed. The zero ring is included by the inherited RingCat interface.

Searches before defining anything (no exact existing match):

- msearch leanfinder: “Restricting sheaves from etale algebraic spaces to etale schemes
  gives an equivalence compatible with ringed topoi and localization”. Eight scheme
  étale-category and affine Γ hits; none on enlarged algebraic-space sites.
- msearch loogle: `"AlgebraicSpace"`: zero hits.
- msearch grep: `enlargedEtale|EnlargedEtale|AlgebraicSpace`: zero Mathlib hits.
- msearch leansearch: “Sheaves on etale algebraic spaces are equivalent by restriction
  to sheaves on etale schemes”. Eight scheme/Zariski hits; none exact.
- Direct rg of WeilConjectures for the item id: zero hits. Direct rg of WeilConjectures,
  lean/Sheaf and the upstream declaration index for enlarged étale notions found only
  prose mentions in the existing module-operation and pushforward-restriction proofs.
  Repeated name searches for IsChartwiseEtale, enlargedRestriction,
  enlargedFibreProduct, chartwiseEtaleMap and schemeSpace found no pre-existing declaration.
- Existing general comparison, subcanonical Yoneda, sheaf precomposition, modules,
  pullbacks and localized topologies were located and reused; they do not themselves
  state this algebraic-space specialization.

Validation: scompile.py compiled the module as a sandbox file and as its intended
library module with no errors or warnings. The final delivery dry run and delivery
repeat the required per-file checks. No global build, direct Git command, live-source
edit, or shared-repository write was performed.

## Second reading by Q132

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
