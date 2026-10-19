## Worker report

`Sheaf.AlgebraicGeometry.AlgebraicSpacePushforwardAtlasEqualizer` states
`AlgebraicGeometry.AlgebraicSpace.moduleDirectImage_atlas_equalizer`, with `sorry`.
There are no new Lean declarations or repaired dependency modules. The repair adds one
definition node recording the already published scheme-as-algebraic-space construction.
The natural-language statement is unchanged.

Hypotheses and clauses, matched to the Lean signature:

- The scheme base is `{S : Scheme.{u}}`; `{X Y : AlgebraicSpace S}` and `f : X ⟶ Y`
  are exactly the two algebraic spaces over it and their morphism.
- The affine scheme over `S` is `U : Over S` with `[IsAffine U.left]`. Its atlas map
  is `p : schemeSpace U ⟶ X`; `hp : IsEtale p.hom.hom` and
  `hs : IsSurjective p.hom.hom` assert representable étaleness and surjectivity.
- An arbitrary small-étale module is `F : X.Modules`, with no quasi-coherence or
  finiteness hypothesis.
- `R : Over S` and `p₁,p₂ : schemeSpace R ⟶ schemeSpace U` present the overlap.
  `IsPullback p₁.hom p₂.hom p.hom p.hom` is its actual sheaf-fibre-product property;
  it includes commutativity and the complete universal property. `h₁,h₂` record
  the projection étaleness needed for restriction charts. No affineness is imposed on R.
  Choosing a presentation of the uniquely specified fibre product adds no hypothesis.
- The expressions `p ≫ f` and `(p₁ ≫ p) ≫ f` are `a` and `b`. The pullback-square
  equality identifies the latter with `(p₂ ≫ p) ≫ f`.
- `(pullback p hp).obj F` represents `F_U = p^*F`: the existing theorem
  `moduleTensorPullback_etale_restriction` supplies its normalized identification
  with tensor pullback. The target coefficient module is restriction of F along
  `p₁ ≫ p`. Restriction is precomposition on charts, so this is canonically
  `p₁^*F_U`; the square gives the same restriction along `p₂ ≫ p`, hence `p₂^*F_U`.
- The existential arrows `ι,r₁,r₂` have the three required direct-image source and
  target objects. They are specified, rather than left arbitrary: the three
  universally quantified chart-projection formulas require exactly the restriction
  of the original compatible family of F sections, first along p and then along
  each overlap projection. `moduleChartTarget` retains the scheme and composes
  its structural map. The two guard conditions mean that `q` is precisely this
  composed chart with the same map to V as `t`. For EVERY t there is such a q,
  because p or the appropriate projection is étale. These conditions therefore
  determine each arrow by all projections of the target limit; they are not an
  assumption of an unspecified comparison map.
- `HEq` in these formulas identifies the same F section when its module is
  presented using equal structural maps. Equality of the underlying chart records
  transports the section module; this is the identity transport, not a freely
  chosen module isomorphism. Both section carriers remain in universe u.
- `hz : ι ≫ (r₁ - r₂) = 0` and
  `Nonempty (IsLimit (KernelFork.ofι ι hz))` assert that this canonical map is
  the kernel of the difference. A kernel arrow is mono, so this gives exactness
  at the first and second terms. No surjectivity at the last term is asserted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, `IsEtale`,
  `IsSurjective`, `EtaleSite`, `Modules`, `pullback`, `etaleMap`, `isEtale_comp`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (the recorded general-site module category, transparently Mathlib's SheafOfModules).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`: `moduleChartTarget`,
  `ModuleChart`, `ModuleDirectImageModel.projection`, `moduleDirectImageModel`,
  `moduleDirectImage` and its specified chart-limit universal property.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etale_fibreProduct_isScheme`, `etaleCover_pullback`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace` is in the signature.
  The new definition node `def-trf-scheme-algebraic-space` records it, together with
  `schemeSheaf_isAlgebraicSpace`, using `existing: true`. The enlarged-site theorem
  stays in `proof_deps`; its restriction equivalence, normalized extensions and cover
  equalizer support the proof.
- Proof-only imports: `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`
  (`chartwise_etale_permanence`) and
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction`
  (`moduleTensorPullback_etale_restriction`, `etale_module_pushforward_restriction`).
  The site-covering and module-category proof dependencies are transitively imported.
- Mathlib's `KernelFork.ofι`, `IsLimit`, and preadditive subtraction express the kernel.

The docstring gives all six proof steps from the node: enlarged-site extension;
base change of the singleton atlas cover; overlap identification over `V ×_Y X`;
normalized étale restriction; the linear sheaf equalizer; and sectionwise module kernels
and functoriality. The source is Stacks `spaces-morphisms.tex`, Tag 03M8. Its printed
subscript X in the overlap formula is the already documented source typo: the correct
base is `V ×_Y X`. The delivery does not repeat that typo or claim right exactness.

Edge cases checked: empty X (including the empty affine atlas), F=0, an identity atlas
when X is an affine scheme, and a nontrivial finite affine atlas of a scheme such as
P¹. The sheaf equalizer and chart normalizations apply in each case. R need not be
affine and f need not be quasi-compact, separated, or étale. No independent universe
restriction, nonemptiness assumption, or sheafification/abelian-structure binder is added.

Searches for an existing declaration (all remote searches used `msearch.py Q87
lem-trf-space-pushforward-atlas-equalizer`):

- LeanFinder: `Direct image of an algebraic space module is the kernel of the
  difference of restrictions from a surjective etale scheme atlas`. Eight hits,
  including `KaehlerDifferential.kerTotal_map`, `Scheme.kerFunctor`, `Scheme.Hom.ker`;
  none concern an algebraic-space module direct-image equalizer.
- Loogle: `SheafOfModules, CategoryTheory.Limits.KernelFork`. No hits.
- Mathlib grep: `atlas.*equalizer|equalizer.*atlas|compute_pushforward`, in
  AlgebraicGeometry. No hits.
- LeanSearch: `A module direct image on an algebraic space is the kernel of the
  difference of two restriction maps from a surjective etale atlas`. Eight hits,
  including scheme Zariski restrictions, `Algebra.FormallyEtale.iff_of_surjective`,
  and `Scheme.Hom.ker`; no match.
- `rg` over `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id,
  `atlas.*equalizer|equalizer.*atlas|moduleDirectImage_atlas_equalizer`: no match.
  Over `lean/Sheaf` it found the downstream quasi-coherent pushforward proof,
  a chart-model proof comment, and unrelated coequalizer remarks; no theorem match.
- DAG grep for `lemma-compute-pushforward` and atlas/equalizer terms found this item,
  the module-operations definition, and the related base-change and quasi-coherence
  nodes, which state different results. `tools/blueprint_refs.py search atlas equalizer`
  found zero blueprint nodes.

Validation: the final module passed both sandbox and named-module compilation through
`scompile.py`, with no errors or warnings. All variables and universe u are explicit.
No statement fault or disputed statement remains.

## Second reading by Q87

This is the resumed worker's separate source-and-signature reading; the maintainer
performs the independent review required by the dispatched brief, which prohibits
starting other agents. I reopened the node, Stacks 03M8, the recorded dependencies,
and the Lean signature. The earlier draft omitted `[IsAffine U.left]`, failed to
specify the overlap universal property, and left the arrows and coefficient comparison
unnormalized. The final statement restores affineness, requires `IsPullback`, and
characterizes all three arrows on every chart. It uses the already normalized étale
restriction functor for the coefficient identifications. I checked that the normalization
guards have a matching composed chart for every t, so they cannot leave the arrows
unconstrained, and that the two routes into X agree by the pullback square.
The three projection formulas and the kernel fork match the canonical restriction,
the two projection restrictions, and the two exactness clauses. The proof docstring
contains all six source steps. The earlier dry run's split blueprint tag and signature
record mismatch are also repaired. No natural-language node correction is needed.


Repair reading: the immutable returned head `42c5692beb6b` was returned solely for H2:
its added theorem statement dependency supplied a plain definition rather than an object
constructed by the theorem conclusion. The resumed packet matched the current main node
outside `lean` and that extra dependency, and its initial dry run passed at `04063686ee`.
The requested repair adds `def-trf-scheme-algebraic-space`, cites it instead, and retains
`lem-trf-space-enlarged-etale-ringed-site-model` in `proof_deps`. The Lean file is unchanged.
I opened both existing declarations: `schemeSpace` contains actual Yoneda sheaf data;
`schemeSheaf_isAlgebraicSpace` is solely the proposition certifying its diagonal and atlas.
This checks every clause of the new node, including precomposition on scheme morphisms,
with no arbitrary object choice and no additional assumption on the scheme. Empty and
non-affine schemes are included. No natural-language item correction is involved.

## New nodes

`def-trf-scheme-algebraic-space` records a scheme over S as its actual representable
fppf sheaf, endowed with its algebraic-space property, using the unchanged published
`schemeSpace` and `schemeSheaf_isAlgebraicSpace` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (`existing: true`). The sources are
Stacks 025Y and the scheme inclusion in 03G1. Its statement dependencies are precisely
`def-pc-scheme`, `def-trf-algebraic-space`, and `def-pc-fppf-site`. LeanSearch for
"A scheme over S gives an algebraic space by its representable fppf sheaf" returned
scheme and local representability declarations; LeanFinder for "A scheme over S
regarded as an algebraic space using the representable fppf sheaf" returned scheme
over-category declarations. Mathlib grep for
`schemeSpace|schemeSheaf_isAlgebraicSpace|IsAlgebraicSpace` found no hits; the same
upstream grep found none. The side-project grep located the two reused declarations.
DAG name/concept searches found theorem-node records and other constructions, but
no definition node owning this construction; blueprint search for the exact phrase
"scheme algebraic space" found zero nodes. The raw search outputs are recorded in
the new node. This adds ownership only, with no duplicate Lean definition.
