## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativeLfpPermanence` states
`AlgebraicGeometry.AlgebraicSpace.mapIsLocallyOfFinitePresentation_of_comp` with
`sorry` as its entire proof. There are no new definitions or other declarations.
The source is Stacks Project, `spaces-morphisms.tex`, Tag 05WT,
`lemma-finite-presentation-permanence`; I read its statement and atlas proof.
The mathematical statement and proof plan of the DAG node are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`, with explicitly bound universe `u`.
- The three algebraic spaces over that same base are `{X Y Z : AlgebraicSpace S}`.
  This is the recorded full subcategory of fppf sheaves with representable diagonal
  and a surjective étale scheme atlas. Its morphisms are natural transformations.
- The two composable morphisms are `(f : X ⟶ Y) (g : Y ⟶ Z)`.
  Lean's `f ≫ g` denotes the node's `g ∘ f`.
- Local finite presentation of the composite is precisely
  `(hfg : MapIsLocallyOfFinitePresentation (f ≫ g))`.
- Local finite type of the second morphism is precisely
  `(hg : MapIsLocally (@LocallyOfFiniteType) g)`.
- The conclusion is exactly `MapIsLocallyOfFinitePresentation f`.
- Both local properties mean the existing universal compatible-étale-scheme-chart
  test. `MapIsLocallyOfFinitePresentation` unfolds to
  `MapIsLocally (@LocallyOfFinitePresentation)`, and the other hypothesis uses
  the same `MapIsLocally` directly with Mathlib's scheme local finite type property.
- No separation, quasi-compactness, quasi-separatedness, Noetherian or characteristic
  assumption occurs in the signature. There is no restriction to representable maps.

The existing landed definition node `def-sfb-space-morphism-properties` was added
only to `stmt_deps`, as permitted by brief-stage2 §5 for already landed notions.
It owns the chart predicates needed to render the node's expressly specified chart
interpretation. No new node, dependency repair or statement correction is needed.
The node copy otherwise changes only `lean`.

Dependency declarations inspected and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsAlgebraicSpace`, `IsEtale`, `IsSurjective` and the full-subcategory
  morphism interface. These supply the precise algebraic spaces of the dependency.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`, the affine-local scheme predicate.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the affine-local scheme predicate.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally` and
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation`.

The following recorded proof dependencies are plain imports, with the node's three
proof steps reproduced in the theorem docstring:

- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace` and
  `etaleCover_pullback` supply fibre products and atlas base changes.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests`:
  `AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests` supplies
  representable surjective étale base change and composition.
- `Sheaf.AlgebraicGeometry.SchemeEtaleSourceTargetProperties`:
  `AlgebraicGeometry.scheme_etale_source_target_properties` gives locality of the
  two scheme finiteness properties.
- `Sheaf.AlgebraicGeometry.SpaceEtalePresentationPropertyCriterion`:
  `AlgebraicGeometry.AlgebraicSpace.etalePresentation_property_criterion`,
  `EtalePresentation` and `HasEtalePresentationProperty` give the universal and
  surjective-source existential chart conditions and their equivalence.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.locallyOfFinitePresentation_of_comp` is the existing closed
  declaration recorded by the audit of `lem-a1-map-over-base-finite-presentation`.
  Its signature takes scheme maps `f`, `g`, local finite presentation of `f ≫ g`,
  and local finite type of `g`, exactly the affine-chart cancellation needed here.
  The dependency has no `lean` record, but its closed audit supplies this declaration;
  no duplicate statement or attachment repair was introduced.

Edge cases checked before writing: an empty source has only empty étale source
charts, so the conclusion is the usual vacuous local finiteness assertion; an empty
Z forces Y and X empty. For `g = id` the conclusion repeats the composite finiteness
hypothesis, and for `f = id` the conclusion is local finite presentation of an identity.
For spaces represented by schemes, the recorded presentation criterion identifies
these chart tests with the scheme properties, recovering Tag 02FV. Arbitrary base
schemes, non-quasi-compact atlases and nonseparated maps remain allowed. The statement
uses the existing size convention at arbitrary `u` and adds no independent smaller
universe for test schemes. There is no index set, dimension or integer parameter.
No statement dispute or source discrepancy was found.

Searches for existing statements, all performed for this item:

- `msearch.py leanfinder`: “If the composite of two morphisms of algebraic spaces is
  locally of finite presentation and the second is locally of finite type then the
  first is locally of finite presentation”. Eight hits: scheme composition,
  scheme finite-type cancellation, ring `AlgHom.FinitePresentation.of_comp_finiteType`,
  and scheme base change. None states cancellation for algebraic spaces.
- `msearch.py loogle`: `"LocallyOfFinitePresentation", "LocallyOfFiniteType"`.
  Three hits: lfp implies lft and the two locally Noetherian equivalence declarations;
  no algebraic-space cancellation theorem.
- `msearch.py grep`: `AlgebraicSpace|locallyOfFinitePresentation_of_comp|of_comp_finiteType`.
  Nine hits, all scheme/ring results. The ring cancellation theorem is an input, not
  the desired algebraic-space statement.
- `msearch.py leansearch`: “A morphism of algebraic spaces is locally of finite
  presentation if its composite is locally of finite presentation and its target
  map is locally of finite type”. Eight hits, again only scheme or ring declarations.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `relative_lfp|finitePresentation_of_comp|locallyOfFinitePresentation_of_comp|MapIsLocallyOfFinitePresentation|MapIsLocally.*FiniteType`
  found the existing upstream scheme theorem, the shared space chart definitions,
  and their consumers, including the downstream diagonal theorem. None states this
  cancellation result for algebraic spaces.
- `grep -rn` of the item id in `lean/WeilConjectures` found no occurrence.
- `rg` for `AlgebraicSpace|mapIsLocallyOfFinitePresentation_of_comp` in
  `dag/lean_names_upstream.json` found no matching declaration. A direct Mathlib and
  upstream name search also found no collision for the new theorem name.

Validation: `scompile.py Q09 lem-sfb-space-relative-lfp-permanence` compiled this
file in sandbox and library module forms against the live published build, cleanly
in 1.6 and 1.5 seconds respectively. The final module has explicit binders,
`autoImplicit false`, source/proof docstrings and only the single expected `sorry`.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
