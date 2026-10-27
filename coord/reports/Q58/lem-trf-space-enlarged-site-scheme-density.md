## Worker report

The module `Sheaf.AlgebraicGeometry.EnlargedSiteSchemeDensity` states
`AlgebraicGeometry.AlgebraicSpace.enlargedSite_scheme_density`, with its sole proof
`sorry`. It introduces no new definitions, no helper axioms and no additional nodes.
The original node statement and accepted stage-1 split are unchanged. The repaired
statement dependencies additionally name the owner of chartwise étaleness.

Read the complete node and all eight statement-dependency nodes, including their
recorded declarations and docstrings. Read Stacks `spaces-properties.tex`, labels
`definition-spaces-etale-site` (03G0), `lemma-compare-etale-sites` (03G1) and
`lemma-functoriality-etale-site` (03G2), including the proof of the latter. These
identify the precise site, inclusion, final object, fibre products and comparison.
The eight-step proof is carried into the theorem docstring with its cited inputs.

Hypothesis and clause correspondence, in the order of the node:

- The base scheme is `{S : Scheme.{u}}`; the arbitrary algebraic space over it is
  `(X : AlgebraicSpace S)`. Its fppf sheaf, representable diagonal and surjective
  étale atlas are the existing full-subcategory data, not extra hypotheses.
- The size convention uses explicit universes `u v w`. Set sheaves have values
  `Type (max (u + 1) w)`, the existing framework's bound for these sites. The
  refinement index `I : Type v` has an arbitrary, independent universe. No site
  or coefficient universe is forced equal to another. Small skeleta are the
  metatheoretic convention of `def-weil-size-convention`, which has no Lean object.
- The chartwise convention, category of objects and all arrows over X, and
  jointly surjective chartwise étale coverings are the published
  `IsChartwiseEtale`, `EnlargedEtaleSite`, `enlargedEtalePrecoverage`. The actual
  scheme-object inclusion is `enlargedSchemeInclusion X`, using `schemeSpace`.
- Site axioms: first conjunct `X.enlargedEtalePrecoverage.IsSiteForCoverings`.
- The particular terminal object: an object `T` with `T.obj = Over.mk (𝟙 X)`
  and `Nonempty (IsTerminal T)`. This identifies X/X, not merely some final object.
- Sheaf fibre products give pullbacks: for all `T U V f g`, the existential
  `P p q` supplies `IsPullback p q f g` in the enlarged site and simultaneously
  `IsPullback p.hom.left.hom q.hom.left.hom f.hom.left.hom g.hom.left.hom`
  in fppf sheaves. Its universal property identifies the apex with the actual
  sheaf fibre product, without prescribing a particular representative.
- Finite limits: `Nonempty (HasFiniteLimits X.EnlargedEtaleSite)`.
- Coverings between scheme objects agree exactly: for each small-site presieve
  R, membership in `X.etalePrecoverage U` is equivalent to membership of
  `R.map (enlargedSchemeInclusion X)` in the enlarged precoverage. Full
  faithfulness below ensures that these account for all arrows between schemes.
- Full faithfulness is `Nonempty (enlargedSchemeInclusion X).FullyFaithful`;
  continuity is its `IsContinuous X.etaleTopology X.enlargedEtaleTopology`.
  The later special-cocontinuity conjunct also includes the source's explicit
  cover-preservation and covering-pullback-preservation conditions for continuity.
- For every covering `Presieve.ofArrows T f` of the image of a small object U,
  the theorem supplies a same-index family `W : I → X.EtaleSite`, atlas arrows
  `a i : i_X(W i) ⟶ T i`, and scheme arrows `b i : W i ⟶ U`.
  `IsEtale (a i).hom.left.hom.hom ∧ IsSurjective (a i).hom.left.hom.hom`
  says the charts are representable étale and surjective, with the existing
  scheme-test definitions. The equation `i_X.map (b i) = a i ≫ f i` gives
  the refinement, and `Presieve.ofArrows W b ∈ X.etalePrecoverage U`
  says its composites are an actual small étale covering.
- Every enlarged object T has a scheme object W and a representable surjective
  étale arrow a whose singleton presieve belongs to the enlarged precoverage.
  This explicitly supplies the singleton scheme covering, including its chart.
- All five comparison conditions: the existing
  `IsSpecialCocontinuousForCoverings X.etalePrecoverage X.enlargedEtalePrecoverage`.
  Its definition was read: cocontinuity, the two continuity clauses, local equality,
  local lifting, and image-object covering density. In particular local fullness
  and faithfulness are included, not inferred from an unrelated dense functor.
- The final clause is `(enlargedRestriction X (Type (max (u + 1) w))).IsEquivalence`.
  `enlargedRestriction` is defined by `sheafPushforwardContinuous` along precisely
  this inclusion, so this is literal restriction on objects and maps, not the
  existence of an unspecified equivalence of the sheaf categories.

Statement-dependency declarations reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsEtale`, `IsSurjective`, `EtaleSite`, `etalePrecoverage`, `etaleTopology`.
- `Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence`: `chartwise_etale_permanence`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`: `Precoverage.IsSiteForCoverings`.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `IsChartwiseEtale`, `EnlargedEtaleSite`, `enlargedEtalePrecoverage`,
  `enlargedSchemeInclusion`, `enlargedRestriction`. The first public import brings
  this published module and the algebraic-space and fibre-product modules publicly.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`.
- `WeilConjectures.CategoryTheory.SpecialCocontinuousCoverings`:
  `Functor.IsSpecialCocontinuousForCoverings`.
- `def-weil-size-convention` records a convention, not a declaration; it is
  implemented by the explicit universe bounds above.

The stated proof dependencies are imported, using plain imports for proof-only
inputs: terminal-plus-pullback finite limits; scheme field-point/residue-field
factorization; common extension fields; representable étale scheme tests; Yoneda
full faithfulness; and the special cocontinuous sheaf equivalence. Existing
statement imports already expose the remaining proof inputs. The definition-owning
`EnlargedEtaleRingedSite` is a downstream DAG consumer imported by the already
published chartwise-permanence interface. A later proof import of this new theorem
into that downstream module must be omitted to avoid an import cycle, as already
noted in the chartwise-permanence node; no new cycle of modules is introduced here.

Edge cases checked before writing: the empty base and empty algebraic space still
have their identity terminal object; no nonemptiness is assumed. The empty covering
index is allowed in the refinement quantifier and yields empty W, a and b, with the
same covering hypothesis and conclusion. Repeated covering arrows are represented
by the existing presieve convention. Atlas choices are one per original index, so
no finite-index restriction or changed refinement index is introduced. The
pullback clause allows arbitrary arrows between objects, not just atlas maps or
scheme-source arrows. There is no representability requirement on a general
chartwise étale object or covering arrow. Arbitrarily large admissible sheaf
universes are represented by the free w. No node fault or statement dispute found.

Searches actually run with `msearch.py Q58 lem-trf-space-enlarged-site-scheme-density`:

- LeanFinder: "The inclusion of scheme objects into the enlarged etale site of an
  algebraic space is fully faithful continuous special cocontinuous and restriction
  is an equivalence of sheaves". Eight hits: scheme étale forgetful full faithfulness,
  schemes' big/small étale topologies, and related declarations. No exact match.
- Loogle: `CategoryTheory.Functor.IsContinuous, CategoryTheory.Functor.IsEquivalence`.
  Zero hits.
- Mathlib grep: `EnlargedEtale|enlargedScheme|scheme.*density|IsCoverDense`,
  restricted to CategoryTheory. Hits concern general dense-site machinery,
  including `DenseSubsite/Basic.lean`; none state this algebraic-space theorem.
- LeanSearch: "algebraic space enlarged etale site scheme inclusion induces
  equivalence of sheaves". Eight hits on schemes' étale and affine Zariski sites
  and generic `Equivalence.sheafCongr`; no exact match.
- Direct ripgrep of both `lean/WeilConjectures` and `lean/Sheaf` for
  `scheme_density|SchemeDensity|scheme-density|enlargedSchemeInclusion.*(full|special|cover)|enlarged.*(density|Density)`:
  no matching declaration. Node-id search in `lean/WeilConjectures` found none.
  Further keyword search `EnlargedEtale|enlargedScheme|scheme_density|IsSpecialCocontinuousForCoverings`
  in both AlgebraicGeometry trees found the published enlarged-site constructions
  and their consumers. Read the complete `EnlargedEtaleRingedSite.lean`:
  `enlargedEtale_site`, `enlargedSchemeInclusion_continuous` and
  `enlargedRestriction_equivalence` cover subsets of the node's conclusions, but
  do not state the cover agreement, full faithfulness, atlas refinement and all
  special-cocontinuity conditions. Reused their definitions and supplied the full
  conjunction, without duplicating any notion.

Validation: prescribed `scompile.py` compiled this file both in its private sandbox
and as `Sheaf.AlgebraicGeometry.EnlargedSiteSchemeDensity` against the live published
library, cleanly (3.6 s and 4.9 s). `autoImplicit false` enforces explicit binding;
maximum line width is at most 100 characters. The node's lean.statement is extracted
verbatim from the theorem signature. No source checkout was edited and no direct
Git command or global build was run.


## Returned delivery repair (2026-10-25)

Repaired the sole required point H2 from the independent review of immutable head
`69aecf85a5de`. Added the already landed definition node
`def-sfb-space-chartwise-etale-morphism` to the item's `stmt_deps`. Read its
statement and existing Lean attachment, then the full signature and docstring of
`AlgebraicGeometry.AlgebraicSpace.IsChartwiseEtale` in
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: it tests every representable
étale scheme chart and requires its composite to be representable étale, without
requiring the original map to be representable. This is precisely the predicate
used by `EnlargedEtaleSite` and `enlargedEtalePrecoverage`. The existing public
import chain through `ChartwiseEtalePermanence` already exposes its owning module.

Compared the retained node with current main before editing: no differences
outside the delivered `lean` record. Refreshed the node copy from current main,
retained that exact `lean` record, and added only the requested dependency. The
Lean module is retained byte-identically to the returned delivery; its recorded
signature still matches verbatim. The report now records the repaired dependency.
No statement correction, dependency replacement or new definition is necessary.
The review's suggestion about independent ownership of other enlarged-site
definitions is advisory; the required repair changes only this dependency list.

Validation is repeated with the prescribed server compile, delivery dry run and
delivery wrapper. The maintainer supplies the independent second reading.

## Second reading by Q58

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
