## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceAffineModuleBaseChange` states
`AlgebraicGeometry.AlgebraicSpace.affine_moduleDirectImage_baseChange`, with its
only proof `sorry`. It states the ordinary degree-zero assertion of Stacks 07U8,
`spaces-cohomology.tex`, `lemma-affine-base-change`. I read the setup immediately
before `equation-base-change-diagram` and the lemma and proof at lines 1657–1702.
The source's derived vanishing clause belongs to the separate higher-image node;
this item's statement asks precisely for quasi-coherence and ordinary base change.

Clause-by-clause correspondence:

* A scheme S and four algebraic spaces over it: `{S : Scheme.{u}}` and
  `{X Y X' Y' : AlgebraicSpace S}`. The arbitrary universe `u` is explicit;
  the existing site and module constructions keep their published universes.
* The morphisms f, g and the projections h, f': the four explicit morphism binders.
* Representability of f: `hf : IsRepresentable f.hom.hom` is exactly the
  scheme-test definition from `AlgebraicSpace.lean`.
* Affineness on every affine scheme test: `ha : MapIsAffine f`. This existing
  predicate quantifies over every `T : Over S`, its affineness and every
  `yoneda.obj T ⟶ Y.obj.obj`, and supplies an affine U and a representing
  presheaf pullback square. It is the affine-test clause of the node, without
  a second definition. Keeping `hf` explicitly renders the node's separate
  representability clause as well.
* X' is X times_Y Y', with its projections: `sq : IsPullback h.hom f'.hom
  f.hom g.hom` in fppf sheaves. The full subcategory universal property of
  algebraic spaces identifies this with exactly the required fibre product.
  Quantifying over a representing square avoids choosing a special presentation.
* A quasi-coherent structure-module sheaf F on X's small etale site:
  `(F : X.Modules) [F.IsQuasicoherent]`. `Modules` is the existing
  `ringedSiteModules.{u} X.structureSheaf`, and the predicate is Mathlib's
  local presentation by arbitrary coproducts, not a finite presentation.
* The first conclusion is `((moduleDirectImage f).obj F).IsQuasicoherent`.
* The second is `IsIso ((moduleBaseChange f g h f'
  (ObjectProperty.hom_ext _ sq.w)).app F)`.
  The equality is precisely commutativity supplied by the pullback square,
  transported through the full subcategory. No comparison map is assumed.
* The required definition of beta is inherited verbatim: `moduleBaseChange`
  transposes `moduleBaseChangeCounit` through `moduleTensorAdjunction f'`.
  The latter first uses `moduleTensorSquare`, then h-star of the specified
  counit for f. `moduleTensorSquare` composes `moduleTensorComposition f' g`,
  equality of the composites, and the inverse of `moduleTensorComposition h f`.
  These are fixed by their local tensor formula and units. Thus the direction
  is g-star f_* F to f'_* h-star F, with exactly the specified adjoint.
* Naturality in F is part of the type of the existing natural transformation.
  The theorem asserts invertibility of its component, not an unrelated iso.
* There is no flatness, finite-type, finite-presentation or Noetherian assumption
  on g, and no finiteness assumption on F; the displayed binders are exhaustive.

The statement and its source are unchanged. `stmt_deps` gains two definition
nodes, one landed and one new ownership record:
`def-sfb-space-affine-quasifinite-properties` for `MapIsAffine`, and
`def-sfb-space-module-base-change` for the canonical comparison helpers.
The latter is a new existing:true ownership record added in this H2 repair,
and cites the already landed `def-sfb-space-module-tensor-composition`.
The theorem node `lem-sfb-space-flat-direct-image-base-change` is removed from
`stmt_deps`; its flat base-change conclusion is not assumed or applied.

Dependency interfaces read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `IsRepresentableWith`, `IsRepresentable`, `EtaleSite`, `structureSheaf`, `Modules`.
* `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`;
  this supplies the recorded scheme-affine notion and proof permanence inputs.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineQuasiFinite`: `MapIsAffine`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`.
* `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`: `QCoh`, its slice
  sheafification instances, and the existing `SheafOfModules.IsQuasicoherent`.
* `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `ModuleDirectImageModel`, `moduleDirectImage`, `moduleTensorPullback`,
  `moduleTensorAdjunction`, `moduleTensorSection`. The direct image is fixed by
  all compatible-chart section projections and their limit universal property.
* `Sheaf.AlgebraicGeometry.AtlasEtaleRestriction`, publicly importing
  `SmallEnlargedEtaleModules` and `EnlargedEtaleRingedSite`: the canonical enlarged
  ringed site, restriction equivalences and `chartwiseEtaleMap_continuous`.
* `Sheaf.AlgebraicGeometry.SpaceChartTensorRealization`:
  `space_chart_adjunction_tensor_realization`, including the unit-normalized
  tensor comparison, composition formula and etale restriction formulas.
* `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`:
  `moduleTensorComposition`, `moduleTensorSquare`, `moduleBaseChangeCounit`,
  `moduleBaseChange`. The helper definitions have real data.

All recorded statement-dependency modules are public imports. Stated proof
dependencies are plain imports: etale module pushforward restriction, scheme
Zariski/etale quasi-coherent equivalence, upstream affine pushforward/base change,
chartwise etale permanence, module pullback quasi-coherence, the Zariski/etale
functor comparison square, and Mathlib affine permanence (including separatedness
and affine finite coproducts). The five-step proof docstring follows the node's
proof, including its essential check of the actual map on local tensors.

Edge cases checked before writing: zero F and the empty spaces give the unique
zero-module comparison; no nonempty atlas or index is assumed. Identity f or g
uses the same normalized comparison, rather than excluding identity squares.
The affine tensor inverse `(r' tensor b) tensor m` to `r' tensor bm` uses only
balancing, so nonflat R to R' remains allowed, including quotients and the zero
ring. Arbitrary module presentations remain allowed. Y' is an arbitrary algebraic
space, and every base-change chart in the proof is separately refined by schemes.
No additional coefficient/site universe equality is imposed.

Searches actually run with the prescribed `msearch.py` for Q88 and this item:

* `leanfinder`: "Affine direct image of quasi coherent modules on algebraic
  spaces commutes with arbitrary base change". Eight hits, including scheme
  pushforward, its adjunction and composition; no algebraic-space affine theorem.
* `loogle`: "SheafOfModules.pullback, SheafOfModules.pushforward". Twelve hits,
  including pullback, its adjunction and composition; no requested affine theorem.
* `grep`: "baseChange|base_change", subdirectory `AlgebraicGeometry/Modules`.
  Zero hits.
* `rg` on both `lean/WeilConjectures` and `lean/Sheaf` for affine/base-change,
  module-base-change and tensor-composition names, plus the exact node-id grep
  in `WeilConjectures`: the upstream affine theorem is about schemes, the space
  flat theorem assumes a flat base map and scheme targets, and its canonical
  helper map is reusable. No declaration states this item's theorem.
* Inspection of `AlgebraicSpaceAffineQuasiFinite.lean` found the exact existing
  affine-test predicate. The H2 repair adds only a definition-node ownership record for the existing
  comparison construction; no dependency module or new Lean construction is needed.

Validation: `scompile.py Q88 lem-sfb-space-affine-module-base-change` compiled
the delivered file in both sandbox and library module contexts on the server,
exit 0; no errors or unexpected warnings. The tool privately compiled the newly
landed tensor-realization dependency as well. All variables and the universe
are explicitly bound, with `set_option autoImplicit false`.

No STATEMENT-DISPUTED flag and no statement correction.


## New nodes

`def-sfb-space-module-base-change` owns exactly the three existing definitions
`moduleTensorSquare`, `moduleBaseChangeCounit` and `moduleBaseChange` in the
unchanged module `Sheaf.AlgebraicGeometry.SpaceFlatDirectImageBaseChange`.
The square is allowed to be any commuting square. Its first comparison is
`moduleTensorComposition f' g`, transport along the equality of composites,
and the inverse of `moduleTensorComposition h f`; its second definition
whiskers the specified counit of `moduleTensorAdjunction f`; its final definition
transposes through `moduleTensorAdjunction f'`. This is exactly the canonical
map specified in the item's statement. Its source is Stacks 03D7/03D8 and the
ordinary comparison in 07U8/073K. The node cites the already landed
`def-sfb-space-module-tensor-composition`, which owns the normalized composition
and its unique local-tensor characterization. No theorem is added, and no
existing Lean definition is copied or edited.

New-node searches run during this repair: LeanSearch and LeanFinder each gave
eight results about generic sheaf or scheme pullback adjunctions; Mathlib grep
`moduleBaseChange|moduleTensorSquare|baseChange` in `Algebra/Category/ModuleCat`
gave six scalar-extension hits, with no algebraic-space comparison.
The exact queries and returned declaration/file lists are retained in the new
node's `mathlib_searches`. Local rg in `lean/WeilConjectures`, `lean/Sheaf` and
`dag/nodes` found only the existing three definitions and their old theorem-node
record; there was no separate definition-node owner. `blueprint_refs.py search
'module base change'` returned zero matches. `blueprint_refs.py ancestor` confirms
the inherited null ancestor, retained with the item's via prepended by this item.

## Repair of H2 and self-check

The return at immutable head `884355569d7e` identified only the statement-dependency
ownership fault. The initial saved-packet dry run passed at `dbcdaa31dd6`, which
confirmed mechanical validity but did not repair that fault. This packet adds the
new definition node above and replaces the flat-base-change theorem node by it
in the item's `stmt_deps`. The Lean module and its signature remain byte-identical.
The item differs from the current read-clone base only in `lean` and `stmt_deps`.

I re-read the three definition bodies and the tensor composition definition and
its unique characterization. The new node's arbitrary commuting-square equality
is exactly `w : h ≫ f = f' ≫ g`; it imposes no pullback, flatness or module
condition. Its three maps have precisely the types stated above; the counit mate
has direction `g^* f_*` to `f'_* h^*`. The item's square remains any `IsPullback`,
its affine hypothesis remains representability plus the affine-test predicate,
and its conclusions remain quasi-coherence and invertibility of this canonical
map for every quasi-coherent module. Empty spaces, zero modules and identity
maps are admitted, as are non-flat base morphisms and modules with arbitrary
presentations. No statement correction or new postponed theorem is involved.
This section is a worker self-check, not an independent second reading; the
maintainer independently reviews the delivery as specified in this brief.

Repair validation: the unchanged delivered Lean file compiled cleanly with
`scompile.py` in sandbox (4.1 s) and library (2.0 s) contexts. A read-only
statement/proof dependency traversal from the new definition reached 135 nodes
and did not reach this item, so the ownership repair introduces no cycle.

The repaired-packet preflight first required the current schema field
`import_flags`; the new definition node now supplies the empty list.

## Second reading by Q88

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
