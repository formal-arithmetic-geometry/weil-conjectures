## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEventuallySmooth` states
`AlgebraicGeometry.AlgebraicSpace.eventually_smooth_of_affine_isLimit` with `sorry`.
It introduces no definitions and proves nothing. The mathematical statement is unchanged.
Only `lean` and two additions to `stmt_deps` change in the item JSON.
`def-sfb-proper-curve-moduli` owns the existing scheme-target local-property and
quasi-compactness predicates. The new definition node
`def-sfb-space-etale-presentation-property` owns the two existing presentation
declarations used to state smoothness of the pullback projections. The criterion
theorem remains a proof dependency. No existing dependency node is modified.

Clause-by-clause correspondence:

- Schemes and algebraic spaces are `Scheme.{u}`, `Over S`, and `AlgebraicSpace S`.
  The auxiliary fixed scheme `S` is the base of the existing algebraic-space encoding;
  no geometric condition is imposed on it. In particular one may take the terminal
  scheme, so this encoding does not restrict the schemes in the node.
- The small nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. Using the schemes' universe for the index
  follows the size convention and does not introduce an independent smaller index bound.
- The inverse system is `D : Iᵒᵖ ⥤ Over S`. Its underlying schemes are all affine by
  `hD : ∀ i : Iᵒᵖ, IsAffine (D.obj i).left`. Every transition between these affine
  schemes is automatically affine; a redundant affine-transition hypothesis is omitted.
- `c : Cone D` supplies the limit base and its compatible maps over `S`, and
  `hc : IsLimit ((Over.forget S).mapCone c)` requires exactly the limiting universal
  property on underlying schemes. Thus the limit is not merely a limit in a smaller
  subcategory. Its underlying scheme is `c.pt.left`.
- The fixed stage is `i₀ : I`. The model is `X₀ : AlgebraicSpace S` and the actual
  structural map is `f₀ : X₀.obj.obj ⟶ yoneda.obj (D.obj (op i₀))`.
- Local finite presentation is
  `hlfp : MapToSchemeIsLocally (@LocallyOfFinitePresentation) X₀ (D.obj (op i₀)) f₀`.
  Its defining quantifier tests the induced scheme map on every representable étale
  scheme chart of `X₀`, with the target chart the identity of its scheme base. The
  presentation criterion and scheme étale locality identify this with the chartwise
  local finite presentation in the node, including arbitrary target charts.
- Quasi-compactness is `hqc : MapIsQuasiCompact f₀`. Its definition tests every affine
  scheme mapping to the target and requires compactness of the point space of the
  inverse image, exactly as the node specifies.
- Quasi-separatedness is
  `hqs : MapIsQuasiCompact (pullback.diagonal f₀)`. The diagonal is the canonical
  presheaf diagonal; its underlying sheaf map is the representable diagonal of the space.
  These three hypotheses together are precisely finite presentation. In particular,
  the statement does not silently replace finite presentation by local finite presentation.
- The preliminary sentence defining separatedness does not assume separatedness of
  `f₀`. No separatedness binder is present, and no closed-immersion condition is added.
- The base change `X → T` is the second projection
  `Limits.pullback.snd f₀ (yoneda.map (c.π.app (op i₀)))`. These are actual presheaf
  fibre products, canonically the underlying presheaves of the sheaf fibre products:
  limits of sheaves are computed on their underlying presheaves. Algebraicity follows
  from the recorded fibre-product theorem. No arbitrary comparison map is supplied.
- Limit smoothness is `hf : HasEtalePresentationProperty (@Smooth) (...)` on that
  second projection. This existing definition says that a representable étale
  presentation with surjective source has a smooth horizontal scheme map. The
  presentation criterion identifies it with smoothness tested on every presentation.
  It applies to presheaf maps, so no new choice of a bundled pullback space is required.
- The conclusion is `∃ (j : I) (hj : i₀ ≤ j), ∀ (i : I) (hi : j ≤ i), ...`.
  `D.map (homOfLE (hj.trans hi)).op` is exactly `Tᵢ → Tᵢ₀`, and its Yoneda image
  defines the canonical pullback projection `Xᵢ → Tᵢ`. The same existing smoothness
  predicate is required for every such `i`, not just for one stage.
- There is no surjectivity condition on any transition, no Noetherian assumption,
  and no separation assumption on the model or the auxiliary base.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsRepresentable`, `IsEtale`, and `IsSurjective` (the predicates used by presentations).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth` and
  `smooth_isStableUnderBaseChange`; its affine-local smooth-ring definition is the
  recorded smoothness notion. Relative dimension and étaleness clauses of the
  definition node are not used by this theorem.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, with its full affine-open signature.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, and
  `etale_fibreProduct_isScheme`.
- `Sheaf.AlgebraicGeometry.ProperCurveModuli`: `MapToSchemeIsLocally` and
  `MapIsQuasiCompact`. No proper-curve condition is used.
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `EtalePresentation`, `HasEtalePresentationProperty`,
  `etalePresentation_property_criterion`, and `etalePresentation_property_iff_scheme`.
- `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`:
  `scheme_etale_source_target_properties` (proof dependency, plain import).
- `WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage`:
  `Scheme.exists_smooth_stage_of_affine_diagram` (proof dependency, plain import).
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`:
  `IsProper.isStableUnderBaseChange`, the recorded primary module for
  `lem-pc-proper-base-change`; this proof uses only the other recorded declaration,
  `smooth_isStableUnderBaseChange`, in the already public smoothness module.
- `def-weil-size-convention` is metatheoretic, with no module or declaration to import.
  The explicit `universe u` and index universe implement it.

The proof dependency `lem-trf-space-qc-finite-affine-atlas-refinement` currently has
no `lean` record; therefore it has no module to import. It is needed only for the
postponed proof, not for stating this item. The theorem docstring reproduces all four
accepted proof steps and names every proof dependency, including this atlas lemma.

Source read: `literature/stacks-project/spaces-limits.tex`, Situation
`situation-descent-property` and `lemma-descend-smooth` (084W and 0CN2), including
its proof. The source chooses affine étale presentations and reduces to the scheme
smoothness-descent theorem, as the accepted DAG proof does. Persistence is smooth
base change. The current blueprint tree was searched for the supporting statement;
this is an auxiliary node, not the blueprint unit's own statement.

Edge cases checked before writing and again after compilation:

- Empty `X₀` is permitted. Affine atlases and étale presentations allow empty schemes;
  scheme smoothness imposes no source-nonemptiness condition.
- The zero ring and empty affine base are permitted by `IsAffine` and `Scheme`.
- A singleton directed set is allowed, and the eventual conclusion then includes its
  unique stage. There is no requirement of a strict inequality or a nontrivial transition.
- The empty index set is excluded as the source requires (and the chosen `i₀` already
  witnesses nonemptiness). The tail contains `i₀`, and preorder antisymmetry is not used.
- Non-surjective transition maps, non-Noetherian rings and nonseparated models are
  allowed. Smoothness is assumed for the limit projection, never for a transition map.
- Arbitrarily large small directed diagrams are represented by choosing `u` large enough
  for their indices and the schemes; there is no independent too-small index universe.

Searches (actual tool calls, no exact existing algebraic-space theorem found):

- `msearch.py ... leanfinder`: “A finitely presented algebraic space over an inverse
  limit of affine schemes that is smooth at the limit is smooth at every sufficiently
  large stage”. Eight hits: scheme `IsSmooth`/standard-smooth chart properties,
  `Algebra.smoothLocus_eq_univ_iff`, and ring smoothness definitions. None gives the
  algebraic-space descent theorem.
- `msearch.py ... loogle`: `"Smooth", "limit"` returned zero hits.
- `msearch.py ... grep`: `AlgebraicSpace|[Ss]mooth.*(limit|stage)|eventually.*[Ss]mooth`
  in `AlgebraicGeometry` returned zero hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for eventual smoothness and
  `exists_smooth_stage` found the scheme-only affine diagram/source/limit results,
  `NoetherianApproximation.exists_smooth_stage`, and
  `AlgebraicGeometry.exists_eventually_smooth_of_isLimit_qcqs` in
  `Sheaf.AlgebraicGeometry.DescendSmoothQcqs`. The last has scheme sources and targets,
  so it is not the algebraic-space statement. Its full signature was opened.
- `grep -rn 'lem-sfb-space-eventually-smooth' lean/WeilConjectures` returned no hits.
- Searches of `dag/lean_names_upstream.json`, `lean/Sheaf`, and `lean/WeilConjectures`
  for `eventually_smooth_of_affine_isLimit` found no preexisting declaration.
- Searches of the existing algebraic-space modules found and reused
  `MapToSchemeIsLocally`, `MapIsQuasiCompact`, and `HasEtalePresentationProperty`;
  no private replacement of these notions was introduced.

No mathematical statement dispute or correction, dependency module, or hollow definition.
The H2 repair adds one definition node bound to existing declarations; see below.

Validation: `scompile.py Q14 lem-sfb-space-eventually-smooth` compiled the delivered
file cleanly as both sandbox and library module (1.5 s and 1.6 s respectively).

## Second reading by Q14

This is the worker's final self-audit; the maintainer supplies the independent review,
as required by the dispatcher brief. I reopened the node and final module, compared
all binders and the entire conclusion, and checked the definitions of the three existing
property predicates. The main potential mismatch was confusing local finite presentation
with finite presentation; the final signature explicitly retains both `hqc` and `hqs`.
I checked the direction of the opposite-category arrow: `hj.trans hi : i₀ ≤ i` gives
`Tᵢ → Tᵢ₀`, and `pullback.snd` therefore has target `Tᵢ`. `hc` explicitly refers to
the underlying scheme cone. Smoothness is the same presentation predicate at the limit
and in the conclusion, with its equivalence to all chart tests supplied by the recorded
presentation theorem. The existential stage includes `hj`, and the universal later-stage
quantifier includes equality, so no persistence clause is lost. No mismatch remains.


## Repair of returned head c222c2c66daf

H2 is repaired by replacing `lem-sfb-space-etale-presentation-property-criterion`
in the delivered item's `stmt_deps` with the new definition node
`def-sfb-space-etale-presentation-property`. The criterion remains in `proof_deps`.
The current main node was reread and used as the base, retaining its fields except
for the authorized `lean` record and statement-dependency additions. The returned
Lean file is unchanged, as the maintainer explicitly allowed; this repair changes
the DAG ownership of the existing definitions, not the accepted theorem signature.

## New nodes

`def-sfb-space-etale-presentation-property` records the existing
`AlgebraicGeometry.AlgebraicSpace.EtalePresentation` structure and
`AlgebraicGeometry.AlgebraicSpace.HasEtalePresentationProperty` definition in
`Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`, with
`existing: true`. No module is added, no declaration copied, and no proof supplied.
The source is Stacks 03MJ, its displayed diagram and condition (2), and the following
`definition-P`. Its three statement dependencies are exactly `def-pc-scheme`,
`def-trf-algebraic-space`, and `def-weil-etale-morphism`, as requested.

The TeX quantifies over the same general presheaf map as the Lean declarations.
Its schemes `U,V` correspond to fields `U,V : Over S`; `a,b` are the Yoneda
chart maps, and representable etaleness corresponds to `source_etale` and
`target_etale`. The commuting square is exactly field `comm`. The presentation
property is the existential over `D : EtalePresentation f`, with
`IsSurjective D.a` and `P D.h.left`. It places no surjectivity condition on `b`
and imposes no locality assumption merely to form the predicate. It restricts to
algebraic-space morphisms as in Stacks; equivalence with all presentations is a
separate theorem, which remains a proof dependency. Empty schemes are allowed,
and source surjectivity is imposed only in the existential property.

New searches were run for this definition: LeanSearch for etale presentation
diagrams and properties returned eight ring-presentation or scheme-locality hits;
Loogle for `"EtalePresentation"` returned twelve standard etale ring-presentation
hits; Mathlib grep for `EtalePresentation|HasEtalePresentationProperty` returned
ten unrelated ring-presentation hits. The exact search-tool log records are in
the new node. Source grep found these definitions only in the existing Sheaf module.
Scanning all definition-node declaration records found no owner of either name;
`blueprint_refs.py search 'etale presentation'` found zero blueprint nodes.
Thus this is ownership metadata for existing definitions, not a duplicate notion.

The final repair self-reading checked the new definition node and unchanged
consumer together: the new node owns the exact predicate in both hypothesis and
conclusion, its signature is verbatim, and the criterion theorem is used only
as the postponed proof input. This addresses the maintainer's sole return point.
