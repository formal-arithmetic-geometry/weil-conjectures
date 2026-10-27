## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceHigherImageEtaleRestriction` states the canonical
étale base-change comparison for module direct images. Its main theorem is
`AlgebraicGeometry.AlgebraicSpace.derived_moduleDirectImage_etale_restriction`;
`higher_moduleDirectImage_etale_restriction` gives the requested nonnegative-degree
natural isomorphism. Both proofs are `sorry`. The two helper definitions contain actual
composites of the already normalized ordinary comparison, its tensor-restriction
identifications, and the units of the existing module equivalences. No new category,
module operation, tensor pullback, or derived direct image is introduced.

The source was read locally: `literature/stacks-project/spaces-properties.tex`,
lemma-pushforward-etale-base-change-modules (Tag 03LX), together with the preceding
étale-exact-pullback lemma and restriction convention. The source assumes precisely
a cartesian square of algebraic spaces over a scheme and an étale lower horizontal map.
The strengthened derived presentation follows the explicit stage-2 derived-form rule;
the per-degree corollary is supplied as that rule requires. The node's statement,
proof and proof dependencies are unchanged.

Clause-by-clause rendering:

- The scheme is `{S : Scheme.{u}}`; the four spaces are
  `{X Y X' Y' : AlgebraicSpace S}`. All four arrows are explicit morphisms of this
  category, so all are over the same S.
- The sole geometric condition on the base change is
  `hg : IsEtale g.hom.hom`. This is representable étaleness from the recorded
  algebraic-space definition. No surjectivity condition is added.
- `hp : IsPullback h.hom f'.hom f.hom g.hom` says that X' with its specified arrows
  is the sheaf fibre product. This is invariant under the unique pullback isomorphism;
  the fibre-product dependency supplies algebraicity of that product. It neither
  chooses a scheme presentation of Y' nor assumes X' is a scheme.
- Modules are the existing `X.Modules`, equivalently `X.SmallModules` via the recorded
  `X.smallModuleEquivalence`. This equivalence is actual restriction to a small affine
  étale basis, with original coefficient universe u. It covers every module, without
  a quasi-coherence restriction. Testing the second theorem on
  `X.smallModuleRestriction.obj M` therefore gives the assertion for every original M;
  applying the target inverse equivalence gives it in `Y'.Modules`.
- The right derived direct image is the existing `derivedDirectImage f`. The per-degree
  theorem applies `DerivedCategory.singleFunctor X.SmallModules 0` followed by that
  functor and `DerivedCategory.homologyFunctor ... (q : ℤ)`. This is R^q f_* on
  modules by injective-resolution comparison, not a derived functor of QCoh. Ordinary
  injective resolutions compute these values, as in `InjectiveResolution.isoRightDerivedObj`.
- `(q : ℕ)` ranges over exactly the integers q >= 0, including zero. The second
  statement is an isomorphism of functors from all small-model modules, rather than
  unrelated object isomorphisms: its naturality covers every module morphism.
- The restrictions are precisely `smallModuleTensorPullback g` and
  `smallModuleTensorPullback h`, the existing tensor pullbacks conjugated by the fixed
  equivalences. `moduleTensorPullback_etale_restriction` identifies them with localized
  site restriction. No arbitrary restriction functor is supplied as a hypothesis.
- The main derived theorem states `∃! beta` with the square against
  `Functor.rightDerivedFunctorCompUnit` on every homotopy-category object. The other
  side of that square is `Qh.map` of the ordinary comparison on complexes. This fixes
  the canonical comparison by its right-derived universal units, and includes its
  degree-zero normalization. Exact restriction commutes with homology; this gives
  the per-degree functor isomorphism. The main theorem controls its canonical choice.
- The `HasDerivedCategory.{w}` binders merely select localizations, with arbitrary
  common morphism universe w; they do not impose a geometric condition. The
  small-model object and section universes retain the existing convention and are
  not identified by any new universe equality.
- There is no properness, quasi-compactness, Noetherianity, or quasi-coherence binder.

Recorded dependency declarations used and read:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`, `EtaleSite`,
  `structureSheaf`, `Modules`, `pullback`, `etaleMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, the sheaf pullback universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`. The direct image is normalized by
  every chart projection; the adjunction retains the tensor unit.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`:
  `etale_module_pushforward_restriction` and `moduleTensorPullback_etale_restriction`.
  Their normalized existential witnesses are used directly, including the witness
  that h is étale. The equations on all chart sections and local tensors determine
  the chosen isomorphisms, as permitted for universal-property constructions.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation for Mathlib `SheafOfModules`, with its sectionwise-linear
  morphisms and inherited abelian structure.
- `Mathlib.CategoryTheory.Abelian.RightDerived`: `Functor.rightDerived`,
  `InjectiveResolution.isoRightDerivedObj`, `isoRightDerivedObj_hom_naturality`;
  `Mathlib.CategoryTheory.Abelian.Injective.Resolution`: `InjectiveResolution.desc`.
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` and `.Resolution` provide
  `Injective` and `InjectiveResolution`. These are exactly the recorded injective
  resolution and left-exact-additive interfaces, not new definitions.
- Added already-landed dependencies `def-sfb-space-small-ringed-model`,
  `def-sfb-space-derived-module-calculus`, `def-sfb-space-derived-tensor-pullback`:
  their modules `AlgebraicSpaceSmallRingedModel`, `AlgebraicSpaceDerivedModules`,
  `SpaceDerivedTensorPullback` provide `smallModuleEquivalence`,
  `smallModuleDirectImage`, `derivedDirectImage`, `smallModuleTensorPullback` and
  the required existing additivity/K-injective-resolution instances.
- The imported proof plan includes `SpaceCotangentRingMap` (the enlarged ringed-site
  model's current recorded module), `ChartwiseEtalePermanence`,
  `LocalizedModuleExactForSystems`, the recorded right-adjoint injective-preservation
  module, `RingedSiteKInjectiveResolutionsOfUniverses`, Mathlib Grothendieck enough
  injectives, and exact-functor homology. The natural-language proof follows all six
  node proof steps, including extension by zero, resolution lifting and independence.

Edge cases checked mathematically: q = 0 recovers the ordinary chart comparison
through the augmented resolution; M = 0 gives zero on both sides; empty source or
empty base-change space gives zero restrictions; g = identity retains every module
and reduces to the ordinary normalized identification; a non-surjective étale map
works because extension by zero and restriction require no cover hypothesis;
non-quasi-coherent modules are included. The main derived square is stated on all
unbounded complexes, whose K-injective restriction is justified by the exact left
adjoint on complexes. No boundedness condition is introduced. All variables and
universes are explicit, and `autoImplicit false` is enabled.

Searches for an existing statement:

- `msearch.py ... leanfinder "Higher direct images of modules on algebraic spaces
  commute with etale restriction"`: 8 hits, including scheme open restriction and
  ordinary scheme direct image. No algebraic-space module higher-image theorem.
- `msearch.py ... loogle "CategoryTheory.Functor.rightDerived,
  CategoryTheory.InjectiveResolution.isoRightDerivedObj"`: 8 hits. Found the exact
  classical resolution-computation API and its naturality; no geometric base change.
- `msearch.py ... grep "rightDerived.*(comp|iso)|etale.*higher|higher.*etale"
  CategoryTheory`: 22 hits, general right-derived comparison machinery only.
- `rg` of `lean/WeilConjectures/AlgebraicGeometry` for higher-image/étale material
  found scheme/abelian/coefficient comparisons, not this structure-module theorem on
  algebraic spaces. Search for this exact node id in `lean/WeilConjectures` had no hit.
- `rg` of `lean/Sheaf/AlgebraicGeometry/AlgebraicSpace*.lean` and wider Sheaf searches
  found the existing small-model derived operations, affine vanishing, and
  quasi-coherent higher-image theorem. The last cites this item in its proof but
  does not supply the arbitrary-module étale restriction statement. The normalized
  ordinary comparison was reused rather than restated.

Validation: scompile.py compiled sandbox and library module modes cleanly (5.8 s and
6.1 s in the first successful run). A final dry run also compiles the delivered module.
No statement dispute, correction, missing definition node, or dependency repair.

## Second reading by Q35

Worker self-check, with the node and final file open; no other agent was started,
as explicitly required by the dispatcher brief. The maintainer supplies the independent
review. I compared each geometric binder, the cartesian square, arbitrary modules,
nonnegative degree, tensor restrictions and naturality against the node. The small
model is an existing equivalence in the original section universe, not a restriction
on the modules. The main unique isomorphism includes the canonical unit equation;
the second theorem gives all nonnegative cohomology functors. The two helper defs
use the recorded chart-normalized witnesses and only equivalence cancellation.
Every theorem proof is sorry; definitions have complete data. No mathematical
statement mismatch was found. During compilation, `Functor.isoWhiskerLeft/Right`
needed the explicit Functor namespace opening; this was fixed. Unneeded auxiliary
exactness/injective-preservation statements were removed: these are proof steps,
not extra geometric hypotheses or independent postponed declarations.
