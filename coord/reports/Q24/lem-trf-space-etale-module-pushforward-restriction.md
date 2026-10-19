## Worker report

The delivery states `lem-trf-space-etale-module-pushforward-restriction` in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleModulePushforwardRestriction` and supplies
its missing canonical module-functor interface in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`. This is stage 2: all
postponed propositions are named theorems with `sorry` and source/proof docstrings;
definitions have data. No statement correction or disputed statement is needed.

The hypotheses and clauses are rendered as follows.

- The base is explicitly `{S : Scheme.{u}}`; `X Y X' Y' : AlgebraicSpace S` use the
  dependency's actual fppf-sheaf algebraic spaces. The arbitrary morphisms are
  `f : X ⟶ Y`, `g : Y' ⟶ Y`, `h : X' ⟶ X`, and `f' : X' ⟶ Y'`.
- The sole etaleness hypothesis is `hg : IsEtale g.hom.hom`. There is no
  representability, surjectivity, separation, finiteness or quasi-coherence
  hypothesis on `f` or on the modules.
- `hp : IsPullback h.hom f'.hom f.hom g.hom` says that `X'` with its named
  projections is the fibre product of the underlying fppf sheaves. Algebraic
  spaces are the recorded full subcategory, so this is precisely the specified
  fibre-product square, allowing any chosen representative. `hp.w` supplies
  commutativity; an independent equation is not a hypothesis. The conclusion
  returns `hh : IsEtale h.hom.hom`, rather than assuming it.
- The natural isomorphism `beta` has source
  `moduleDirectImage f ⋙ pullback g hg` and target
  `pullback h hh ⋙ moduleDirectImage f'`. The existing dependency's `pullback`
  is etale restriction on module sheaves, with its actual structure-sheaf map.
- For each `F : X.Modules`, etale scheme `V : Y'.EtaleSite`, and scheme chart
  `q : ModuleChart f' V`, the first conjunct equates the chart projection of
  `beta(s)` with the projection of `s` to the same scheme chart, transported by
  `moduleChartBaseChange`. The latter retains the scheme and its map to `V`;
  its commuting triangle is obtained from `hp.w`. The defining limits say
  these projections are exactly all compatible sections on the fibre product.
  Thus the equation specifies identity on those sections, not just existence
  of an unnormalized isomorphism. The natural isomorphism and the model's two
  projection identities encode restriction in `V` and module morphisms in `F`.
  All components are morphisms in the actual sheaf-of-modules categories.
- For every etale map (rename `g` to `u`), `etaleRingRestriction` is restriction
  of ring sheaves along the existing etale site functor.
  `etaleStructureRestrictionIso` is the identity isomorphism on the actual
  structure sheaves: their regular functions, operations and restrictions are
  definitionally identical. This expresses `u⁻¹𝒪_Z ≅ 𝒪_Z'` on the localized
  etale sites.
- `moduleTensorPullback_etale_restriction` supplies a natural isomorphism
  `moduleTensorPullback u ≅ pullback u hu`. Its equation for every chart,
  scalar `a`, and section `m` is the multiplication formula `a ⊗ m ↦ a m`,
  using the actual chart restriction. Thus tensor pullback is restriction,
  including scalar structure and the unit normalization, for every etale map.
- The second isomorphism `lambda` has source
  `moduleTensorPullback f ⋙ pullback h hh` and target
  `pullback g hg ⋙ moduleTensorPullback f'`. Its equation fixes the local
  tensor `a ⊗ (b ⊗ m)` as `(a * b) ⊗ m`, preserving `m`. Both `a` and `b`
  live on the same underlying scheme chart: restriction along `h` keeps that
  scheme and its regular functions. `moduleTensorSection` uses the retained
  adjunction unit followed by its specified chart projection and multiplication
  by the scalar, so this is an equation about the canonical tensors. It does
  not assume arbitrary global sections are pure tensors. Naturality in `G`
  and compatibility of the two paths are included in this natural isomorphism
  and its normalization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `.IsEtale`, `.EtaleSite`, `.etaleTopology`,
  `.structureSheaf`, `.Modules`, `.etaleMap`, `.etaleMap_isContinuous`, and
  `.pullback`. In particular the last declaration is etale module restriction,
  not an already-existing pullback for arbitrary space morphisms.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`
  (used through the preceding module's `Modules`); its definition is exactly
  Mathlib's `SheafOfModules`, with the stated coefficient universe.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`: the recorded
  sheaf tensor interface; its actual tensor construction and local `tmul`
  normalization were read. The present arbitrary-morphism pullback is fixed by
  the equivalent tensor/direct-image adjunction, with its unit retained.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme` in the algebraic-space namespace. These give
  the recorded fibre-product interpretation and the proof input that `h` is
  etale, by the family `{g,id}`. They are imported with their existing interface.
- Proof-only sources were also read:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`, including
  `SheafOfModules.overFunctor`/`overMap`, and
  `Sheaf.Paper.LocalizeRingedSiteMorphismGeneral`, including
  `SheafOfModules.localize_ringed_site_morphism_general`. These are the recorded
  ringed-localization inputs. The enlarged-site-model proof node has no usable
  module-functor declaration. The new definition instead fixes exactly the
  required canonical operations directly by their chart universal property;
  it does not assume a chosen arbitrary functor or require the entire enlarged
  site model as additional statement data. The unchanged proof can use that
  enlarged-site node when it is proved.

Edge cases checked before finalizing the statement: identity `g` and identity
`f` yield the unit-normalized identity comparisons; an empty etale base change
and a non-surjective open etale map impose no surjectivity assumption; zero
modules give the zero compatible families; arbitrary nonrepresentable `f` is
allowed because the chart category does not require `X ×_Y V` to be a scheme.
The formula is local before sheafification, so it does not require global
pure-tensor representatives. The chart category has scheme-object universe
`u+1` while section modules have the dependency's universe `u`. The existence
proof uses the small descent equalizer on a scheme atlas; it does not assert
that a raw product indexed by all charts lies in `u`, nor add a universe equality.

Searches (the raw launcher results are retained in `searches.jsonl`):

- `msearch.py ... leanfinder` with “Etale localization of algebraic spaces
  commutes with module direct image and tensor pullback”: eight algebra/ring
  etaleness hits, no matching space-module statement.
- `msearch.py ... loogle` with
  `SheafOfModules.pushforward, SheafOfModules.pullback, Functor.rightKanExtension`:
  zero hits (the final identifier was unknown); generic pushforward/pullback
  declarations were independently located and read.
- `msearch.py ... leansearch` with “Canonical direct image of modules on the
  etale site of an algebraic space is compatible sections on scheme charts,
  tensor pullback is its left adjoint”: eight hits, comprising the generic
  `SheafOfModules.pullback`/adjunction and scheme-module functors, none supplying
  the arbitrary algebraic-space chart-section normalization.
- `msearch.py ... grep` with
  `AlgebraicSpace|pushforward.*restrict|restrict.*pushforward`: seventeen generic
  module/site and scheme/Zariski hits, no match. A second grep for
  `compatible.*section|directImage.*[Mm]odule|[Mm]odule.*[Dd]irectImage` under
  `AlgebraicGeometry` found only an unrelated gluing occurrence.
- Direct `rg` searches in Mathlib, upstream `WeilConjectures`, and side
  `lean/Sheaf` found no existing declarations with the new operation names;
  the item-id upstream search had no hit. DAG text searches and
  `tools/blueprint_refs.py search` for “module direct image algebraic space”
  and “compatible sections” found no existing definition of this interface.
  The enlarged-site theorem node was read: it concerns a ringed-site model,
  not this module-functor universal property, and carries no recorded Lean
  declaration supplying these operations.

## New nodes

`def-trf-space-etale-module-functors` defines canonical module operations for an
arbitrary morphism of algebraic spaces. Source: Stacks Tags 03G8 and 03H7 for the
ringed topos and chart extension, 03M8 for compatible-section direct image, and
03D7 for the tensor/direct-image adjunction. The module constructs the chart
category, scalar pullbacks of regular functions, chart restriction maps and
diagram. `ModuleDirectImageModel` specifies a limit cone for every evaluation,
and both naturality identities. `moduleDirectImageModel_unique` states uniqueness
of the natural isomorphism preserving every projection. Selecting such a model
is therefore the universal-property construction expressly permitted by AGENTS.md
section 5, rather than a choice from a mere existence assertion that leaves the
object undetermined. The left adjoint is likewise fixed with its adjunction unit;
`moduleTensorSection` defines its canonical local tensors from that unit.
Supporting theorem declarations (linearity, diagram laws, existence, uniqueness,
and right-adjointness) are part of this one definition's interface, listed in
`lean.declarations`, and have source and complete natural-language proofs. The
three search kinds above, plus Mathlib/upstream/side/DAG/blueprint searches, found
no existing definition with this normalized universal property. The item's only
non-lean change is addition of this new definition to `stmt_deps`.

## Validation

Resumed the saved packet and ran the required dry run first. Its compiler
diagnostic identified an unresolved source chart in `moduleChartBaseChange`.
The constructor now explicitly supplies `(etaleMap h hh).obj q.left`; this
retains exactly the chart intended by the original definition and resolves
the subsequent dependent section and scalar types. One source-docstring line
was wrapped to the required 100-character limit. Neither repair changes a
declaration signature or the mathematical statement.

Both delivered modules compiled cleanly together, each as a separate file,
through `scompile.py` on 2026-10-17. The recorded primary signatures were
checked verbatim against their source files. The item differs from the current
repository only in `lean` and the added definition dependency in `stmt_deps`;
the new definition node remains absent from the current repository. A current
search of Mathlib, upstream `WeilConjectures`, and side `lean/Sheaf` found no
duplicate of the delivered declarations. Every source line is at most 100
characters, and all theorem proofs remain `sorry`.

## Second reading by Q24

Independent maintainer reading of the immutable delivery ce2e97dc2a6cc873e8f8b39dbb16a46abb216c14 on 2026-10-18. The item, every statement dependency, both delivered modules, their actual dependency declarations, and the Stacks sources were opened.

- Base and objects: `S : Scheme.{u}` and `X Y X' Y' : AlgebraicSpace S` use the recorded full subcategory of fppf sheaves. `f` is arbitrary; `hg` is the recorded etale notion for `g`. No finiteness, quasi-coherence, surjectivity, or extra universe equation is assumed.
- Square: `hp : IsPullback h.hom f'.hom f.hom g.hom` expresses the specified fibre product up to its unique isomorphism. The conclusion produces `hh`, rather than assuming base-change etaleness. The family `{g,id_Y}` in the proof supplies it even for non-surjective `g`.
- Direct image: `ModuleChart` contains the actual scheme maps and commuting triangles. `moduleChartScalar`, `moduleChartMap`, and `moduleChartDiagram` retain regular-function pullbacks and actual module restrictions. `ModuleDirectImageModel.isLimit`, `map_projection`, and `restriction_projection` specify compatible sections and both naturalities. Its normalized uniqueness theorem justifies selection by universal property under AGENTS section 5; this is not arbitrary functor data.
- First comparison: `beta` has precisely `(f_*F)|Y'` and `f'_*(F|X')` as endpoints. Its equation at every `V`, chart `q`, and section `s` preserves every limit projection. `moduleChartBaseChange` keeps the underlying scheme and its map to `V`; `hp.w` supplies its triangle. Thus the equation is identity on compatible chart sections, with scalars and both naturalities retained.
- Etale restriction: `etaleRingRestriction` is precomposition along the existing site functor. `etaleStructureRestrictionIso` is reflexivity because the underlying schemes, regular functions, and their maps are identical. `moduleTensorPullback_etale_restriction` fixes its natural isomorphism by `a tensor m` mapping to `a` times the actual restriction of `m`.
- Tensor comparison: the left adjoint and its retained adjunction define `moduleTensorSection` from the unit and the specified projection. Uniqueness of adjoints identifies this with tensor pullback, compatibly with the unit. `lambda` has exactly the two requested paths as endpoints; its second equation preserves `m` and multiplies `a` and `b` on the same underlying scheme. This is a local generator formula, not an assertion that all sheaf sections are globally pure tensors.
- Dependencies: read `Scheme`, `AlgebraicSpace`, `ringedSiteModules`/`SheafOfModules`, the independent-universe tensor interface and `siteSheafTensorTmul`, and all three fibre-product/cover declarations. These are the stated notions; no private replacement is used. Read the generic ringed-localization declaration and the enlarged-site node for the documented proof route. The new operations interface is part of the missing canonical construction permitted in this delivery.
- Sources: spaces-properties.tex Tags 03G8, 03H7, 03LV, 03LW, and 03LX (including the pullback footnote), spaces-morphisms.tex Tag 03M8, and sites-modules.tex Tag 03D7 agree with the statement. Corrected the erroneous adjunction tag 03CR to 03D7 in the new definition record, its module docstrings, and this report. Tag 03CR instead concerns presentation of ringed-topos morphisms by ringed sites.
- Edge cases: empty base/empty etale localization, zero modules, identity maps, non-surjective etale maps, and nonrepresentable `f` are admitted. The chart indexing category has object universe `u+1`, but section modules are in `u`; an atlas and its scheme overlap give the small descent equalizer, so no equality of independent site/coefficient universes is required.
- One-definition search: independently searched Mathlib, upstream WeilConjectures, and the group side tree for the operation names and compatible-section/direct-image terminology. Generic site functors and Zariski scheme functors do not supply this normalized algebraic-space interface. The worker records LeanSearch, Loogle/LeanFinder, and grep searches. The added node has the required definition fields and is cited by the item.
- Gates: source/blueprint docstrings are present, both primary signatures are verbatim, all variables and universes are bound, all nine theorem proofs are only `sorry`, definitions have real data or uniquely determined universal-property data, and every source line is within 100 characters. No source statement correction, citer audit, pro-etale substitute, or dropped route-pivot node is involved.

Compiler reproduction on 2026-10-18: supplied both immutable sibling modules to `scompile.py` in dependency order. It passed with exit code 0 and no diagnostics, checking every module separately; final library checks took 34.7 s (operations) and 52.7 s (item). An earlier consumer-only invocation failed for the absent undelivered sibling, then the complete two-file overlay resolved it. The citation-only replacement leaves the complete Lean code unchanged. No global build or live Lean write was performed.

Findings repaired: H11, the original second-reading placeholder; H8/B5, the incorrect adjunction source tag. No mathematical statement or declaration signature changed. The independent review record at review.md records the compiler reproduction and all findings.
