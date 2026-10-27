## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceGeometricStalkTensorCalculus` defines
`AlgebraicGeometry.AlgebraicSpace.geometricStalkPullbackComplexIso` and states
`AlgebraicGeometry.AlgebraicSpace.geometricStalk_tensor_calculus`. The only new
postponed proof is the latter theorem, with the item's six-step proof in its
docstring. The complex isomorphism is constructed by applying
`NatIso.mapHomologicalComplex` to the already recorded, germ-normalized
`SingleComplex.pullbackStalkIso`; it has no postponed data or proof.

The sources read were Stacks `spaces-perfect.tex`, equation-bc and
`lemma-single-complex-base-change-condition` (0DKG), especially the geometric
stalk setup and the strict-henselization comparison; `spaces-properties.tex`,
`lemma-stalk-pullback-quasi-coherent` (05VQ); `sites-modules.tex`,
`lemma-pullback-stalk` (05V5); `sites-cohomology.tex`,
`lemma-check-K-flat-stalks` (0DEN); and `examples.tex`, `section-silly`
(0FLS), the paragraph specifying flatness of can_z and observing that the tensor
source need not be local. The ordinary formula for arbitrary modules is 05V5,
rather than the quasi-coherent specialization 05VQ.

Hypothesis and clause correspondence:

* The base scheme is `{S : Scheme.{u}}`; the four algebraic spaces over it are
  `{X X' Y Y' : AlgebraicSpace S}`. This uses the recorded fppf-sheaf definition,
  not schemes substituted for spaces.
* The four maps are `f`, `f'`, `g`, `g'`, and
  `sq : IsPullback g' f' f g` says that X' with these projections is the fibre
  product. Quantifying over a cartesian realization avoids making any extra
  choice of a categorical pullback and includes every such realization.
* The geometric point has `{Ω : Type u} [Field Ω] [IsAlgClosed Ω]`,
  `s : Spec (.of Ω) ⟶ S`, and
  `x : yoneda.obj (Over.mk s) ⟶ X'.obj.obj`. This is the Yoneda presentation
  of the stated geometric point over S, using the same Ω for all its images.
* The image point on X is `x ≫ g'.hom.hom`; on Y' it is
  `x ≫ f'.hom.hom`; on Y it is `(x ≫ g'.hom.hom) ≫ f.hom.hom`.
  The already recorded `point_square` transports the alternative path through Y'.
* R is `SingleComplex.R f g' s x`; A is
  `SingleComplex.stalkRing s (x ≫ g'.hom.hom)`; B is
  `SingleComplex.stalkRing s (x ≫ f'.hom.hom)`; C is
  `SingleComplex.stalkRing s x`. Each `stalkRing` is the ring colimit in
  `StalkModel`, with the actual regular-function cocone and module-section germs.
  Its pointed affine basis is cofinal in the pointed etale neighbourhoods.
* D and its map to C are the existing `SingleComplex.tensorMap f f' g g' sq s x`.
  The existing `leftAlgebra` and `rightAlgebra` give the R-actions, and
  `tensorMap_existsUnique` specifies the restrictions to both projection stalk
  maps. No arbitrary map or assumption identifying D with C appears.
* Flatness is the first conjunct `(tensorMap f f' g g' sq s x).Flat`.
  This is exactly `RingHom.Flat`, i.e. flatness of C as a module over D via
  the specified map, equivalently exactness of extension of scalars.
* The first displayed formula, for every original-site complex, is the real
  definition `geometricStalkPullbackComplexIso h s z M` with `h = g'`.
  Its left side is ordinary scalar extension of the source stalk complex and
  its right side the stalk of ordinary tensor pullback. The orientation is
  opposite to the display in the node and is inverted to read that display.
  The scalar-extension convention writes C tensor_A M rather than M tensor_A C;
  A is commutative, so this is the usual symmetric tensor convention.
* For the second formula the theorem works in the already recorded equivalent
  small module categories. `S_A` and `S_C` are the exact stalk functors after
  localization: `e_A` and `e_C` identify their composites with Q with the
  localized termwise stalks. Such factorizations determine the functors up to
  the unique compatible localization isomorphism. `L`, `ε`, and
  `L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso ... (.up ℤ))` specify
  total derived extension along the actual ring homomorphism `stalkMap g' s x`.
  The natural isomorphism `j : S_A ⋙ L ≅ derivedPullback g' ⋙ S_C` is thus the
  second formula, in D(C), simultaneously for every derived object. Its inverse
  has the orientation displayed in the node.
* The final equation is stated for every `M : CochainComplex X.SmallModules ℤ`.
  Starting at Q(M_x), its left side uses the localization factor `e_A.inv`,
  `j`, the stalk of the specified pullback derived counit, and `e_C.hom`.
  Its right side uses the scalar-extension derived counit `ε` and Q of the
  normalized `tensorStalkIso`. This is precisely equality of the two
  derived-to-ordinary maps after the displayed identifications. On K-flat
  representatives the counits are invertible, so the equation also fixes the
  canonical derived isomorphism, not merely its source and target.
* There is no boundedness, quasi-coherence, or flatness assumption on f or g.
  `DerivedQCoh` is context in the node, not a restriction on M; the imported
  quasi-coherence and derived-module interfaces already supply that notion.

Universes: u is the original section/scheme universe used by the normalized
geometric stalk interface. The derived categories of the sheaf small models
use w, as required by the existing `derivedPullback`. The ring-module
localizations use independent wA and wC: no equality between the sheaf or ring
localization sizes is imposed. `HasDerivedCategory` binders choose the
localizations of the given categories and are the size convention, not an
additional mathematical exactness or resolution assumption. All universes and
variables are explicitly bound; `autoImplicit` is false.

Dependency declarations read and reused:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `EtaleSite`, `structureSheaf`, `Modules`.
* `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, using
  Mathlib `SheafOfModules.IsQuasicoherent` with the original local-presentation
  meaning. The node's quasi-coherent context adds no hypothesis here.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`.
* `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, with `Module.Flat`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceGeometricStalkModels`:
  `SingleComplex.StalkModel`, `stalkModel`, `stalkRing`, `stalk`, `stalkMap`,
  `pullbackStalkIso`, `smallPullbackStalkIso` and their germ normalization.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedPullbackModels`:
  `SingleComplex.pullback`, `derivedPullback`, `counit`, `FlatKFlat`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceSingleComplexStalkCondition`:
  `SingleComplex.R`, `leftAlgebra`, `rightAlgebra`, `point_square`,
  `tensorMap`, `stalkComplex`, `extendedStalkComplex`, `tensorStalkIso`.
* `Sheaf.AlgebraicGeometry.SpaceDerivedModuleOperations`:
  `moduleTensorPullback_additive`, needed to map original-site pullback complexes.

The last four owning definition nodes are added to stmt_deps as already-landed
interfaces, under brief-stage2 section 5. No new node or dependency repair is
needed, and the natural-language statement and proof are unchanged. A dependency
traversal found no path from any added dependency back to the item.

All recorded proof dependencies have plain imports and were read: fibre products
and etale covers, representable etale scheme tests, `geometricStalk_flat_iff`
and its strict-local chart comparison, `Scheme.strictHenselization_triples`,
`RingHom.indEtale_principalZariski_stability`, `RingHom.IndEtaleAcrossUniverses`,
`RingedSitePoint`, `RingedSitePoint.tensor`,
`CochainComplex.ringedSite_kFlat_stalk_criterion`, and `RingedSitePoint.exact`.
The statement dependencies use public imports, including their canonical
universal-property constructions; none is copied or replaced.

Edge cases checked before writing:

* An empty X' has no geometric point over a field; the pointwise assertions are
  correctly vacuous, without a nonemptiness hypothesis on any space.
* Zero complexes and unbounded complexes are included. The counit equation is
  quantified over every integer-indexed complex, not just flat or K-flat ones.
* Neither an identity projection nor a nonflat projection is excluded. Flatness
  is asserted only for D to C and is not assumed for f or g.
* D is not required to be local or isomorphic to C; 0FLS explicitly cautions
  against that identification. The statement uses the tensorMap universal property.
* The same algebraically closed field and its same map to S determine all four
  stalks. There is no independent smaller test-point universe.
* The small-site equivalence includes every original module complex. The
  ordinary formula is also exposed directly on original-site complexes.

Searches actually run:

* `msearch.py ... leanfinder`, query "Geometric stalks of algebraic space fibre
  products are flat over tensor products and stalks commute with derived tensor
  pullback": eight hits, including `AlgebraicGeometry.Flat.stalkMap` and the
  scheme pullback-triplet tensor declarations. They concern schemes, ordinary
  scheme stalks, or require flatness of a scheme morphism, so none states this item.
* `msearch.py ... loogle`, query `ModuleCat.extendScalars, RingHom.Flat`:
  `ModuleCat.preservesFiniteLimits_extendScalars_of_flat`, which takes the
  flatness of the ring map as input and does not prove this geometric map flat.
* `msearch.py ... grep`, regex `stalk.*[Tt]ensor|[Tt]ensor.*stalk`: twenty
  Mathlib hits, concerning prime spectra, rank, and surjectivity on stalks.
  No algebraic-space geometric derived comparison was returned.
* `rg` of `lean/WeilConjectures` for the item id, stalk/tensor terms, and
  `rg` of `lean/Sheaf` for geometric stalks, derived stalks and scalar comparison:
  upstream scheme-only `SingleComplexBaseChange.exists_stalkDerivedExtensionComparison`
  is analogous but uses ordinary scheme stalks. The existing algebraic-space
  geometric stalk model and single-complex condition supply the canonical
  constructions reused here; neither asserts their fibre-product flatness or
  the natural derived comparison. Constant-coefficient scheme-stalk tensor
  declarations also have different rings and objects.
* `rg` for the two proposed declaration names in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  no existing declaration with either name.

No statement dispute or source correction was found. Compilation used only
`scompile.py` against the published live library. An initial compile identified
a missing original-pullback zero-preservation instance; the already-landed
`moduleTensorPullback_additive` was imported from its owner instead of introducing
another theorem. Syntax was repaired, and the module then compiled without
errors or warnings, in about five seconds per wrapper check.

## Second reading by Q17

No second worker was started: the dispatcher brief forbids other agents and
requires direct delivery. The maintainer supplies the independent review.
The worker's final rereading checked the orientations and types of both
localization factors and the scalar counit: the displayed equation starts at
Q(M_x) after derived scalar extension and ends at Q of the stalk of ordinary
pullback on both sides. It uses the existing normalized chain isomorphism and
contains neither a flatness hypothesis on a projection nor a quasi-coherence
restriction on the complex.
