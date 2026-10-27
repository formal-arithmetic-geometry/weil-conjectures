## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion` states
`AlgebraicGeometry.AlgebraicSpace.etalePresentation_property_criterion` and the scheme
comparison `etalePresentation_property_iff_scheme`, each with `sorry`. Its three real
definitions package precisely the locality predicate, the presentation data, and the
extended property introduced in the item's own statement. No theorem is proved and
no definition contains postponed data or a choice of atlas.

The inherited BLOCKED ending was a stage-1 unchanged-item refusal. I read the current
stage handoff in brief-stage2 §0: the reviewed split is the input to this stage, not a
prohibition on adding its Lean record. The item appears as stage 2 in queue.tsv, has no
Lean record, and has no released repair note. Its accepted split is preserved. The only
additional statement dependency is the already landed `def-sfb-space-morphism-properties`,
whose `MapIsLocally` definition supplies exactly condition (1).

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base scheme is `{S : Scheme.{u}}`; schemes over it are `Over S`. The single explicit
  universe `u` matches the recorded algebraic-space presheaves `(Over S)ᵒᵖ ⥤ Type u`.
  Scheme objects occupy `Type (u+1)` and morphisms and section sets occupy `Type u`.
  No extra universe equality, nonemptiness or size restriction is imposed.
- The property of scheme morphisms is `P : MorphismProperty Scheme.{u}`; the explicit
  isomorphism-invariance hypothesis is `[P.RespectsIso]`, Mathlib's pre- and
  postcomposition invariance under isomorphisms.
- Locality is `hP : IsEtaleLocalOnSourceAndTarget P`. The first conjunct states
  `Etale a → P f → P (a ≫ f)` for all composable scheme maps, exactly (i).
- Its second conjunct states `P f → Etale b → P (Limits.pullback.snd f b)`. This is (ii),
  since this second projection has source `X ×_Y V` and target `V`. Switching the two
  pullback factors compared with the source's notation changes only the canonical
  presentation of that base change; the isomorphism-invariance hypothesis covers it.
- Its third conjunct is `P f ↔ ∀ x : X, ∃ U V a b h u, ...`, with both `Etale` conditions,
  `a.base u = x`, `a ≫ f = h ≫ b`, and `P h`, exactly the pointwise criterion (iii).
- Algebraic spaces and their morphism are `{X Y : AlgebraicSpace S} (f : X ⟶ Y)`.
  Their underlying natural transformation is `f.hom.hom`.
- `EtalePresentation f` has `U V : Over S`, natural transformations `a`, `b`, an
  `S`-scheme morphism `h : U ⟶ V`, the two recorded `IsEtale` predicates, and
  `a ≫ f = yoneda.map h ≫ b`. `IsEtale` already includes representability, so this
  does not drop that condition or impose a separate redundant hypothesis.
- Existence is the main theorem's first conjunct
  `∃ D : EtalePresentation f.hom.hom, IsSurjective D.a`.
- Condition (1) is the existing `MapIsLocally P f`. Its full definition quantifies
  over U,V,a,b,h and requires the two representable étale conditions and commutativity
  before concluding `P h.left`. This is exactly quantification over all the
  `EtalePresentation` structures used on the other side.
- Condition (2) is `HasEtalePresentationProperty P f.hom.hom`, defined by
  `∃ D : EtalePresentation f, IsSurjective D.a ∧ P D.h.left`.
  The second main conjunct equates (1) and (2). This definition gives the extended
  property without making a noncanonical choice.
- For schemes the second theorem uses an arbitrary `S`-scheme morphism `f : X ⟶ Y`
  with `X Y : Over S`, viewed through `yoneda.map f`. It asserts both the universal
  presentation condition iff `P f.left`, and the existential condition iff `P f.left`.
  Representing a scheme by Yoneda is its usual fully faithful inclusion; no arbitrary
  comparison map is supplied as an extra assumption.
- Neither theorem nor `EtalePresentation` requires `IsSurjective D.b`. The source
  surjectivity occurs only in the explicitly existential condition and existence claim.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`
  (recorded `def-pc-scheme`); the former is a locally ringed space locally affine,
  the latter a morphism of locally ringed spaces.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`
  (recorded `def-weil-etale-morphism`), read with its affine-open ring-map signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, and `IsSurjective`
  (recorded `def-trf-algebraic-space`). I read the full module. Their tests quantify
  over every scheme mapping to the target and give actual representing pullback squares.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`, the already landed universal chart
  predicate. Its node is added to `stmt_deps` to reuse this definition.
- `def-weil-size-convention` is a metatheoretic convention, with no declaration;
  explicit universe binders implement the same size convention as the dependency.
- Mathlib's `MorphismProperty.RespectsIso`, Yoneda, and chosen scheme pullbacks supply
  isomorphism invariance, natural transformations of representables and (ii).
  All already stated proof dependencies are imported through their recorded modules:
  pullbacks, étale morphisms, covering base change and composition in
  `Mathlib.AlgebraicGeometry.Sites.MorphismProperty`, and Yoneda full faithfulness in
  `Mathlib.CategoryTheory.Yoneda`. The six original proof steps are included in the
  theorem docstrings; none of the source's additional representable-f assertion is claimed.

Edge cases checked before drafting:

- Empty source: the pointwise condition is vacuous, so the locality hypothesis forces P
  on maps from the empty scheme. Both presentation tests respect that case. No
  `Nonempty` instance on any scheme or presentation type is assumed.
- Identity charts: these recover the original scheme property and witness the converse
  direction of the scheme comparison. Arbitrary non-surjective target charts remain
  allowed, including empty target charts when the source chart is empty.
- Non-surjective target chart: the common-refinement proof only uses its étaleness;
  surjectivity of the source chart supplies the lifts needed for locality.
- The everywhere-false property is not étale-local under clause (iii) on the empty
  source; the theorem correctly retains that clause rather than accepting a vacuous
  locality hypothesis. The everywhere-true property satisfies all three clauses.
- No separatedness, quasi-compactness, finite type, characteristic, or surjectivity of
  f itself is added. P is a property of all schemes, not merely of the chosen slice.

Searches performed (2026-10-23):

- `msearch.py leanfinder`: “An etale local source and target property of scheme
  morphisms extends to algebraic spaces and is independent of etale presentations”.
  Eight hits concerned scheme étaleness, Zariski source locality and related facts;
  none stated the algebraic-space presentation criterion.
- `msearch.py loogle`: `"AlgebraicSpace"`, zero hits.
- `msearch.py leansearch`: “A property of scheme morphisms etale local on source and
  target is independent of algebraic space presentations”. Eight hits concerned
  sourceAffineLocally, ring-map locality and scheme properties, not this criterion.
- `msearch.py grep`: `AlgebraicSpace|[Ee]tale[Ll]ocal|[Ll]ocal[Ss]ource[Tt]arget`
  in Mathlib/AlgebraicGeometry, zero hits.
- `rg` of the exact item id in `lean/WeilConjectures`, no match. `rg` of
  `etalePresentation|EtalePresentation|IsEtaleLocalOnSourceAndTarget|etaleLocalSourceTarget`
  in `lean/Sheaf` and `lean/WeilConjectures` found unrelated standard étale algebra
  presentations, lci line diagrams and image filtrations, not this statement.
- Broader searches for `AlgebraicSpace`, `03MJ`, `04QZ`, and local-source-target
  terminology exposed `AlgebraicSpaceMorphismProperties.MapIsLocally`, which is reused.
  `AlgebraicSpaceRepresentableEtaleSchemeTests` supplies scheme tests, not the general
  arbitrary-property equivalence. No existing Lean statement matches the item.
- I opened the actual local Stacks sources at spaces-morphisms.tex
  lemma-local-source-target (03MJ), spaces.tex lemma-lift-morphism-presentations (02X1),
  and descent.tex definition-local-source-target (04QZ). They agree with the node.

No statement correction, new DAG node, dependency repair, or disputed statement is needed.
The local notions are explicitly introduced in this item's own statement, and are
listed in its `lean.declarations`; they are not unstated independent prerequisites.

Validation: the module is compiled only with the prescribed `scompile.py` wrapper;
server compilation and the delivery dry run are required before the final push.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
