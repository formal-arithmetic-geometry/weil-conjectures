## Worker report

The delivery writes `Sheaf.AlgebraicGeometry.ClassicalContinuityMap`, with primary
predicate `AlgebraicGeometry.ProEtale.IsClassical`. This pass checked the inherited
sandbox module against the current node, its detail and proof in `main-20261015`,
and the recorded dependency declarations. The module includes an affine limit
vertex, the limit universal property in all schemes over the base, the intrinsic
constant-ring module category, and actual cohomology sheaves for both complex forms.
No mathematical changes to the inherited module were needed. The node record now
contains the verbatim multiline signature and the current UTC date. The independent
second reader must review this delivery before it is pushed.

Hypotheses and clauses:

- A scheme is `X : Scheme.{u}`; the set sheaf is
  `Sheaf (Scheme.ProEt.topology X) (Type (u + 1))`. The common larger universe
  `u + 1` contains both section values and the objects and morphisms of every index
  category. `I : Type (u + 1)` and `[SmallCategory I]` impose the stated smallness.
  `[IsCofiltered I]` includes nonemptiness. These binders allow categories with
  parallel arrows and do not restrict indexing to posets or sequences.
- Clause 1 is `AffinePresentation X I`. Its `diagram : I ⥤ X.ProEt` supplies
  all stages and transition arrows over `X`; `affine` and `etale` impose the
  absolute affineness of each stage and étaleness of its structure map. `cone`
  supplies the object `U` and the compatible projection arrows in the site;
  `affineVertex : IsAffine cone.pt.left` makes `U` affine. The `isLimit` field is
  `IsLimit ((Scheme.ProEt.forget X).mapCone cone)`, hence gives the universal property
  among **all** schemes over `X`. A chosen limiting cone with vertex `U` is exactly
  a specified identification with the inverse limit. The site uses the recorded
  weakly étale objects and all morphisms over `X`; étale stages have the required
  weakly étale property by the recorded comparison and the existing instance.
- Clause 2 is the presheaf construction `sectionDiagram P F = P.diagram.op ⋙ F`
  and `sectionCocone P F = F.mapCocone P.cone.op`. `continuityMap` is exactly
  `colimit.desc` for this restriction cocone. Thus its source retains the
  presentation, its target is sections at `U`, and uniqueness is the colimit
  universal property, rather than an extra chosen map. `continuityMap_ι` records
  `[i,s] ↦ F(u_i)(s)`, and `continuityMap_natural` records naturality in `F`.
  The construction is generic in the value category so the same map construction
  works for sets and modules; classicality itself is specialized to sheaves.
- Clause 3 for sets is the quantification over every `AffinePresentation` in
  `IsClassical`, with `Function.Bijective (continuityMap P F.obj)`.
  For modules the binder `Λ : Type u` with `[CommRing Λ]` is an arbitrary discrete
  commutative coefficient ring (no finiteness, topology or characteristic condition).
  The binder `F` is the recorded `ringedSiteModules.{u+1}` over the underlying ring
  of the constant commutative ring sheaf of `ULift.{u+1,u} Λ`. This is precisely
  the category inside the recorded `Scheme.proEtaleDerivedCategory X Λ`.
  `moduleSectionPresheaf` uses `PresheafOfModules.restrictScalarsObj` along
  `Functor.whiskerRight (toSheafify ... (Functor.const ...)) (forget₂ ...)`, the
  canonical map from constant scalars into the constant ring sheaf. Its object
  at `V` is therefore `F(V)` with scalar action through `Λ → Λ_X(V)`, expressed
  using the canonical coefficient lift. Its restriction map is the original map
  of `F`, now linear over the lifted ring. There is no arbitrary scalar map.
  `moduleContinuityMap` applies the same colimit construction in
  `ModuleCat.{u+1} (ULift.{u+1,u} Λ)`. These colimits exist for every permitted
  index category, with no additional `HasColimit` hypothesis in module classicality.
  `IsClassicalModule` requires each linear continuity map to be an isomorphism.
  `isClassicalModule_iff` states exactly the equivalence with classicality of the
  underlying sheaf of sets, using `SheafOfModules.toSheaf` and `sheafCompose`
  with `forget AddCommGrpCat`.
- Clause 4 is supplied in both requested forms. `IsClassicalCochainComplex` takes
  a genuine cochain complex in that same intrinsic module category and requires
  `IsClassicalModule Λ (K.homology q)` for every `q : ℤ`. `IsClassicalComplex`
  takes `K : Scheme.proEtaleDerivedCategory X Λ` and requires classicality of
  each object of `DerivedCategory.homologyFunctor` with the standard localization
  instance used by the recorded category. No arbitrary property is accepted.
  `isClassicalComplex_Q_iff` identifies the two forms under localization;
  `isClassicalComplex_iso_iff` states invariance under every derived isomorphism.
  `isClassical_iso_iff` supplies the set-sheaf invariance used in this argument.
- The final paragraph is `affinePresentation_iff`, with `[IsAffine X]` and an
  arbitrary `U : X.ProEt`. Existence of a presentation with vertex isomorphic to
  `U` is equivalent to `proAffineEtale U.hom`, exactly the property defining the
  recorded `Scheme.AffineProEt`. The recorded `proAffineEtale_Spec_iff` identifies
  this property with ind-étaleness over affine `X`. No affine-base assumption is
  imposed on the preceding definitions.

Dependency declarations read and reused:

- `def-weil-pbc-proetale-site`: `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`,
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`; Mathlib
  `Mathlib.AlgebraicGeometry.Sites.Proetale`, `Scheme.ProEt`, `Scheme.ProEt.topology`
  and `Scheme.ProEt.forget`. Site objects have universe `u+1`, morphisms `u`.
- `def-weil-size-convention`: the recorded metatheoretic convention, rendered by
  the explicit universes and small categories, with all colimits in `u+1`.
- `def-weil-pbc-category-colimit`: `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit`, `colimit.desc`, `Cocone`, `IsColimit`, and
  `CategoryTheory.IsFiltered` (the last in `Mathlib.CategoryTheory.Filtered.Basic`).
- `sk-def-pe-morphisms`: `WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale`,
  `AlgebraicGeometry.proAffineEtale`, whose stages are absolutely affine and étale;
  `Algebra.IndEtale`, `RingHom.IndEtale`, and the recorded weakly étale notions.
- `det-pe-morphisms-etale-comparison`: `Sheaf.AlgebraicGeometry.EtaleComparison`,
  `AlgebraicGeometry.etale_indEtale_weaklyEtale_comparison`, particularly its first
  clause that étale morphisms are weakly étale.
- `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`,
  transparently Mathlib `SheafOfModules`; its sections, restrictions and abelian
  structure are the existing ones. Scalar restriction uses the existing Mathlib
  `PresheafOfModules.restrictScalarsObj`, not a copied module structure.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory.Q`; and
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`,
  `DerivedCategory.homologyFunctor` and `homologyFunctorFactors`.
- `def-weil-pbc-ind-etale-basis`:
  `WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine`,
  `Scheme.AffineProEt`, its category, `toProEt`, `precoverage`, and `topology`.
- `def-weil-pbc-ind-etale-algebra`: `Sheaf.RingTheory.IndPrincipalZariski`
  (publicly imported through `EtaleComparison`), `Algebra.IsIndPrincipalZariski`,
  with its public upstream declarations `Algebra.IndEtale`, `Algebra.WeaklyEtale`,
  `AlgebraicGeometry.proAffineEtale_Spec_iff`, and
  `AlgebraicGeometry.weaklyEtale_SpecMap_algebraMap_iff`. Only the ind-étale and
  affine presentation clauses enter the final identification; no second
  ind-étale or affine-basis definition is introduced.

Edge cases: a one-object presentation gives the ordinary restriction map (the
identity presentation gives the identity); the empty scheme and empty affine
stages are permitted. The empty indexing category is excluded exactly by
cofilteredness/nonemptiness. Parallel arrows are included. The zero ring, zero
module sheaf and zero complex satisfy the same definitions without added
hypotheses. All integer degrees, unbounded complexes, arbitrary discrete rings,
and nonaffine base schemes occur. The affine-base qualification is confined to
the final identification. No extra equality between the site-object and
site-morphism universes is imposed.

Searches (the inherited log was checked, and all three services plus grep were repeated):

- `msearch.py ... leansearch`, query “classical pro etale sheaf continuity map
  colimit sections affine etale inverse limit”: eight hits, including scheme
  structure-sheaf continuity, `CategoryTheory.Sheaf.isColimitSheafifyCocone`,
  and `SheafOfModules.Presentation.isColimit`; none defines this notion.
- `msearch.py ... leanfinder`, query “A classical pro etale sheaf has a canonical
  continuity map from the filtered colimit of sections of an affine etale inverse
  system”: eight hits, including structure-sheaf section continuity on scheme
  limits and condensed locally constant colimits. None
  defines classical pro-étale sheaves, module continuity, or classical complexes.
- `msearch.py ... loogle`, query `CategoryTheory.Limits.colimit.desc`: twelve
  generic colimit API hits (`colimit.desc`, `colimit.ι_desc`, `colimit.map_desc`,
  and variants), reused for the canonical construction; no exact item match.
- `msearch.py ... grep`, query
  `classical.*[Ss]heaf|continuityMap|continuity_map`: zero Mathlib hits.
- `rg` in upstream `WeilConjectures` and the shared `lean/Sheaf` and side
  `lean/WeilConjectures` for `IsClassical`, `continuityMap`, `continuity_map`,
  and `ClassicalSheaf`: only the unrelated triangulated-generator predicate.
  Search for the exact node id in upstream `WeilConjectures` gave no hit.
- The existing source files for constant-ring module sheaves and scalar
  restriction were read; the canonical `toSheafify` map and Mathlib scalar
  restriction were reused directly rather than introducing another scalar unit.

No statement correction, new node or dependency repair is needed. Every postponed
assertion is a public named theorem with whole proof `sorry` and a source and
natural-language proof docstring for this node's corresponding clause. All
presentation, restriction-diagram, cocone, continuity-map and predicate data are
constructed without `sorry`. No `STATEMENT-DISPUTED` flag remains.

Validation: this pass ran the prescribed `scompile.py` checks on the inherited
module: sandbox compilation passed in 3.0 seconds and library-path compilation
passed in 3.1 seconds, with no errors or unexpected warnings. The source has no
lines exceeding 100 characters, binds universes explicitly, and disables auto-implicits.
The prescribed delivery dry run checks this packet before handoff to the second reader.

## Second reading by Q32

I independently read the sandbox node and Lean module, the main-20261015 detail
and proof files, the unit `_section.md`, every statement dependency's node and
recorded declaration, and the additional proof-dependency records. There is no
repair note for this item, no `statement_change`, no new definition node and no
dependency module in this packet. The blueprint fixes only a scheme and a discrete
commutative ring throughout; it supplies no Noetherian, separation, finiteness or
characteristic hypothesis. I also read the cited Stacks constructions: Categories
002F/002U and the connected-limit-over-X argument; Algebra 00D6/00D7; Derived
05RT/05RU; and Limits 01YW. Their relevant hypotheses match the node.

My object/hypothesis/conclusion checklist, written from the node before comparing
the Lean, is as follows. Every row passes.

| Node item | Lean rendering and verdict |
| --- | --- |
| An arbitrary scheme X and set sheaf F on its small pro-etale site | `X : Scheme.{u}` and `F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))`. `Scheme.ProEt` is the recorded weakly-etale over-category with all X-morphisms, not a site requiring etale structure maps. Correct. |
| Fixed larger universe for small indices and section colimits | `I : Type (u + 1)` and `[SmallCategory I]`; the set values and lifted module values live in `u + 1`. This is the node's larger colimit universe. Site objects remain in `u + 1` and morphisms in `u`, without identifying the two. Correct. |
| A small cofiltered category, affine U, affine etale stages, X-morphisms and a specified inverse limit over X | `AffinePresentation` binds `[IsCofiltered I]`; `diagram`, `affine`, `etale`, `cone`, `affineVertex`, and `isLimit` render these data separately. In particular `Scheme.ProEt.forget X : X.ProEt ⥤ Over X`, so the limit is in all schemes over X, not merely among site objects. A cone with this universal property is the specified identification with the inverse limit. Correct. |
| The restriction diagram indexed by the opposite category, and its compatible projection maps | `sectionDiagram P F = P.diagram.op ⋙ F` and `sectionCocone P F = F.mapCocone P.cone.op`. The variance and cocone compatibility have the required order. Correct. |
| The unique map from the colimit to sections at the vertex, its formula, dependence on presentation and naturality in F | `continuityMap` is `colimit.desc` for that cocone, not a chosen arbitrary map. `continuityMap_ι` gives its value on every coprojection; `continuityMap_natural` has the correct whiskered transformation and component at the vertex. Its source retains P. Correct. |
| Set classicality for every presentation | `IsClassical` universally quantifies over I, its category/cofiltered structures, and P, and requires `Function.Bijective (continuityMap P F.obj)`. Correct. |
| Arbitrary discrete commutative coefficients and intrinsic constant-ring module sheaves | `Λ : Type u`, `[CommRing Λ]`, and the `ringedSiteModules.{u+1}` binder use exactly the constant ring sheaf and canonical `ULift` of `Scheme.proEtaleDerivedCategory`. No scalar topology or finiteness is assumed. Correct. |
| Canonical coefficient actions, linear continuity map and module classicality | `moduleSectionPresheaf` restricts scalars by `PresheafOfModules.restrictScalarsObj` along the whiskered `toSheafify` unit. Thus the scalar map is the prescribed constant-section map, and its transition maps are the original semilinear restrictions, now linear over the fixed lifted ring. `moduleContinuityMap` is the same colimit construction in `ModuleCat`; `IsClassicalModule` requires `IsIso` for every presentation. No colimit-existence premise is added here. Correct. |
| Equivalence with underlying-set classicality | `isClassicalModule_iff` uses `SheafOfModules.toSheaf` followed by `sheafCompose` with `forget AddCommGrpCat`. The underlying sets and restriction maps are precisely those of F, even after scalar restriction. Correct. |
| Cochain and derived complexes, every cohomological degree and derived invariance | `IsClassicalCochainComplex` tests `K.homology q` for every integer; `IsClassicalComplex` tests the actual `DerivedCategory.homologyFunctor` in the recorded category with its `HasDerivedCategory.standard` instance. `isClassicalComplex_Q_iff` compares the two under Q, and `isClassicalComplex_iso_iff` covers every derived isomorphism. No arbitrary cohomology object or boundedness premise occurs. Correct. |
| Exactly the affine ind-etale basis objects when X is affine | `affinePresentation_iff` has `[IsAffine X]` only here and equates existence of a presentation with vertex isomorphic to U to `proAffineEtale U.hom`. The recorded `Scheme.AffineProEt` is exactly `proAffineEtale.Over ⊤ X`, and the recorded `proAffineEtale_Spec_iff` identifies it with ind-etale algebras. Correct. |

Dependency interfaces checked: `Scheme.proEtaleDerivedCategory` is transparently
the derived category of these intrinsic `SheafOfModules`; `ringedSiteModules` is
the recorded transparent abbreviation of that existing module category.
`etale_indEtale_weaklyEtale_comparison` really gives etale implies weakly etale.
The upstream `proAffineEtale` uses absolutely affine etale stages, and
`Algebra.IndEtale` includes finite presentation through `Algebra.Etale`.
The colimit dependency gives `colimit.desc`, and the derived-category dependency
gives both Q and its genuine factoring cohomology functors. None needs repair.

Edge cases checked: cofilteredness includes nonemptiness, so an empty index
category is excluded exactly as required. Non-posetal categories and parallel
arrows are included. Singleton and identity presentations have the expected
restriction map. Empty schemes and empty affine stages are permitted. There is
no nonzero-ring, positive-characteristic, nonzero-module, nonzero-complex or
degree restriction: the zero ring, zero module sheaf, zero complex, degree zero,
negative degrees and unbounded complexes are included. General nonaffine bases
are included in every definition. The final basis identification alone has an
affine base. The universe-u bound on coefficients matches the recorded category;
the lift changes no ring or module data up to its canonical equivalence.

I checked the potentially subtle index-universe difference in the last theorem:
the presentations here allow indices in `u + 1`, whereas upstream
`proAffineEtale` and `Algebra.IndEtale` use indices in `u`. This is not an added
hypothesis. Over affine X, the category of finitely presented etale R-algebras
mapping to the universe-u coordinate ring B has a universe-u skeleton; the given
filtered presentation implies it is filtered with colimit B. Conversely a small
presentation can be lifted. I expanded the theorem's proof docstring to explain
this reduction and the ring-colimit/algebra-colimit/limit-over-X arguments of
node steps 7--9, rather than silently identifying the two universe levels.

Independent searches, using different wording from the worker:

- LeanFinder through `msearch.py`: “A presheaf sends a cofiltered affine etale
  limit presentation to a filtered colimit of its sections”. Eight hits were
  structure-sheaf/global-section continuity results such as
  `AlgebraicGeometry.nonempty_isColimit_Γ_mapCocone` and
  `exists_appTop_π_eq_of_isAffine_of_isLimit`; none supplies the arbitrary-sheaf
  definition or the module and complex clauses.
- LeanSearch through `msearch.py`: “A sheaf of modules is classical when for each
  affine etale inverse system the canonical filtered colimit map on sections is
  invertible”. Eight hits included `SheafOfModules`, its colimit instances and
  `SheafOfModules.Presentation.isColimit`; none states this criterion.
- Loogle through `msearch.py`, `CategoryTheory.Limits.colimit.desc`: twelve hits
  confirmed the canonical generic colimit API already used here, with no item match.
- Direct `rg` of Mathlib, upstream `WeilConjectures`, shared `lean/Sheaf`, and
  shared `lean/WeilConjectures` for `IsClassical`, `continuityMap`,
  `continuity_map`, `AffinePresentation`, `classicalSheaf` and
  `IsProEtaleClassical`; also searched the exact node id upstream. No existing
  continuity criterion or construction matches the whole node. I opened the
  nearby `Scheme.IsProEtaleClassical` in `ProEtaleLocallyClassicalEtaleCover`:
  it is the essential-image predicate for etale inverse image, and its theorem
  does not state equivalence with this continuity criterion. It therefore cannot
  supply the node's presentation, canonical map, or continuity statement as an
  `existing: true` binding. Its docstring anticipates the comparison, but is not
  a declaration of it. The generic Mathlib API is reused, not redefined.

Repairs made: the original packet omitted explicit non-public imports for the
recorded proof dependencies. I added the module Grothendieck/filtered-colimit,
concrete-colimit, commutative-algebra-colimit, affine etale criterion and Spec
adjunction modules. I also expanded only the final theorem's proof docstring as
described above. All mathematical definitions and theorem signatures were right
and remain verbatim unchanged; no node statement correction is required.

The 17 recorded declarations match the module. Every postponed assertion is a
named theorem with whole proof `sorry` and the source/blueprint/proof docstring;
every definition has real data. The functor-law proofs inside
`moduleSectionPresheaf` merely verify the real functor structure and contain no
postponed proof. There is no private definition, file-local instance or notation,
unbound variable, long Lean line, or unresolved disputed statement. The primary
node `lean.statement` equals the source signature verbatim.

Validation after the repairs: prescribed `scompile.py` passed both the sandbox
compile (4.7 seconds) and the library-path compile (5.4 seconds), with no errors
or warnings. The first relative-path invocation could not read the sandbox file;
rerunning with its absolute path resolved that invocation error.
