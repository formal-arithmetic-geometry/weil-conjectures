## Worker report

Item: lem-sfb-field-groupoid-stabilizer-dimension. Stage 2, group NC, 2026-10-23 UTC.

The module `Sheaf.AlgebraicGeometry.FieldGroupoidStabilizerDimension` states
`AlgebraicGeometry.AlgebraicSpace.fieldGroupoid_dimension_eq_stabilizer`, with one
`sorry`, and the four-step natural-language proof from the accepted split in its
docstring. No theorem is proved. The original statement and proof are unchanged.
The item gains two definition dependencies described below. There is no statement
dispute or statement correction.

The previous ending concerned a stage-1 refusal to reopen an accepted split. The
current node has `status: split`, a passing stage-1 review, no `lean` record and no
released repair note; its queue entry is stage 2. The stage-handoff paragraph of
`coord/brief-stage2.md` therefore applies: this delivery states the accepted node.
The preserved sandbox contained only dispatcher brief markers, with no earlier
module, report, node copy or delivered commit to resume.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node | Lean rendering |
| --- | --- |
| An arbitrary base scheme S | `{S : Scheme.{u}}` |
| A field K | `(K : Type u) [Field K]`, Mathlib's field class, including nontriviality |
| U = Spec K over S | `(b : Spec (CommRingCat.of K) ⟶ S)` and the represented presheaf `yoneda.obj (Over.mk b)` |
| R an algebraic space over S | `(R : AlgebraicSpace S)`, using its recorded fppf-sheaf full-subcategory definition |
| Source and target R → U | `(s t : R.obj.obj ⟶ yoneda.obj (Over.mk b))` |
| Identity, inverse and composition | The displayed natural transformations `e`, `i`, `c`, with `c : Limits.pullback s t ⟶ R.obj.obj` |
| These operations are a groupoid on every test-scheme point, naturally | `hgroupoid : IsPresheafGroupoid s t e i c`; the source, target, identity, inverse and associativity laws are spelled out, and naturality is built into the natural transformations |
| Source is locally of finite type on étale charts | `hs`: for every scheme `V : Over S`, étale map `a : yoneda.obj V ⟶ R.obj.obj`, and induced map `f : V ⟶ Over.mk b` with `a ≫ s = yoneda.map f`, require `LocallyOfFiniteType f.left` |
| Target is locally of finite type on étale charts | The separate identical condition `ht`, with `t` in place of `s` |
| G = U ×_(Δ,U ×_S U,(s,t)) R | `groupoidStabilizer s t`, defined by `Limits.pullback (prod.lift (𝟙 U) (𝟙 U)) (prod.lift s t)` in presheaves on schemes over S |
| dim R = dim G | `etaleDimension R.obj.obj = etaleDimension (groupoidStabilizer s t)` |
| Local scheme dimension is infimum over open neighbourhoods | The existing `topologicalKrullDimAt`, whose definition is exactly this infimum |
| Local space dimension is the value in any étale chart over the point | `etaleLocalDimension F x` takes the supremum of those chart values; they all agree by the étale-descent result invoked in the source definition |
| Global space dimension is the supremum over point classes | `etaleDimension F := ⨆ x : Point F, etaleLocalDimension F x` |

The `f` in `hs` and `ht` is not an arbitrary extra morphism or an extra hypothesis:
every composite from a represented chart to the represented U is uniquely the
Yoneda map of such an `f`. Thus each condition tests every étale scheme chart.
Neither surjectivity of each chart nor finite type, quasi-compactness, separatedness,
reducedness, smoothness or an étale hypothesis on s or t has been imposed.

The stabilizer is the actual categorical pullback of presheaves, retaining the
canonical maps rather than an arbitrary equivalent object. For algebraic spaces,
the sheaf pullback has this underlying presheaf; the representable-diagonal and
atlas argument of `fibreProduct_isAlgebraicSpace` gives algebraicity. Consequently
computing its chart dimension as a presheaf computes exactly the dimension of the
stabilizer algebraic space, without assuming additional data or representability
of R by a scheme. The new dimension functions are defined for all presheaves so
this canonical object can be used directly. Only algebraic-space inputs occur in
the mathematical theorem. No arbitrary choice, existence axiom, hollow definition
or chart-independence hypothesis is used in these constructions.

Dependency declarations inspected and used:

- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `IsAlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`, `IsEtale`.
  This is the recorded interface of `def-trf-algebraic-space`.
- Mathlib `Algebra.Field.Defs`: `Field`, extending `CommRing` and `DivisionRing`.
  This is the `mathlib_match` of `def-weil-field`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`, the recorded declaration of
  `def-weil-finite-type-morphism`. Only local finite type is required here.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, its projections and universal property, the
  recorded declaration of `def-pc-fibre-product`. It applies to presheaves as well
  as schemes. Product in presheaves over S represents product over S.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses`:
  `AlgebraicGeometry.AlgebraicSpace.Point`, `schemePointMap`, the recorded interface
  of `def-a1-algebraic-space-point-classes`. Point representatives and their
  common-field-extension quotient are reused, not redeclared.
- `WeilConjectures.Mathlib.Topology.KrullDimension`: `topologicalKrullDimAt`,
  the recorded declaration of `def-kun-topological-dimension-at-point`.
- The two new modules below supply `IsPresheafGroupoid`, `groupoidStabilizer`,
  `etaleLocalDimension`, and `etaleDimension`.

Recorded proof interfaces are imported as plain proof imports: the algebraic-space
fibre-product and chart-permanence modules, flat-lfp source descent, reduction
universal homeomorphism, scheme reduction, étaleness and affine spectrum. Mathlib
matches without `lean` records are also represented by their modules: affine
fibre products by `Mathlib.AlgebraicGeometry.Pullbacks`, proper/finite-presentation
permanence by its recorded morphism-property modules, and the affine-target
correspondence by `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
The constant-local-dimension, scalar-field-uniqueness and finite-type-component
proof nodes have no Lean interface yet; no module can presently be imported for
them. They are used in the proof docstring and remain the accepted proof plan.
All statement dependencies have usable declarations.

Edge cases checked before drafting:

- Empty R cannot satisfy the identity law over the nonempty Spec K; it has not
  been excluded by an added nonemptiness hypothesis. The stabilizer also contains
  the identity. The dimension construction itself allows an empty space and gives
  bottom for its empty supremum.
- For s = t, the groupoid is a group over K, the canonical stabilizer is R, and
  the equality has the expected identity case. The unit groupoid gives dimension 0.
- Nilpotents, inseparable fields, arbitrary characteristics and infinite families
  of components are allowed. No finite-dimensionality assumption is introduced.
- s and t need not agree: the theorem retains both maps and both local finite type
  conditions. The equal-source/target constraint is imposed only in the stabilizer.
- Scheme points and test fields use the same fixed universe u as Scheme and the
  algebraic-space foundations. No independent smaller test universe or extra
  universe equality is introduced. All universes and variables are explicitly
  bound, and all modules set `autoImplicit false`.
- The generic point of the affine line distinguishes the required dimension
  from stalk dimension: the stalk is a field, of dimension 0, whereas every open
  neighbourhood has dimension 1. Thus `etaleChart_localDimension` in
  `AlgebraicSpaceLocalDimensionChartInvariance` cannot be used to define this node's
  local dimension. Its signature and docstring were read; it is about ring dimension.
- In the groupoid definition the first factor is the later arrow. The laws give
  `c(i(a),a) = e(s(a))`, `c(a,i(a)) = e(t(a))`; associativity uses the overlapping
  pairs `(a,b)` and `(b,d)`. This agrees with the source convention.

Searches performed for the item:

- `msearch.py leanfinder`, query "Dimension of an algebraic space groupoid over a
  field equals dimension of its stabilizer": eight unrelated presentation,
  smoothness and fixed-field dimension hits, no match.
- `msearch.py loogle`, query `"Groupoid", "dimension"`: zero hits.
- `msearch.py grep`, query
  `groupoid.*dimension|stabilizer.*dimension|GroupoidObject` in CategoryTheory:
  zero hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream-name index for
  groupoid/stabilizer dimension, `FieldGroupoid`, and the proposed declaration
  names: no existing theorem or general internal-presheaf-groupoid definition.
  The prescribed node-id grep in `lean/WeilConjectures` found no declaration.
- `rg` and a parsed title/statement scan of definition nodes, and
  `tools/blueprint_refs.py search groupoid` / `search algebraic space dimension`:
  found the scheme-only groupoid definitions, the existing topological dimension
  definitions, and moduli groupoids, but no definition of either missing notion.
- For each new node, separate LeanSearch, LeanFinder and Mathlib grep searches
  were performed. Their complete wrapper outputs, together with source grep
  results and the duplicate-node assessment, are recorded in `mathlib_searches`.
  Semantic search returned ordinary groupoids, manifold groupoids, étale scheme
  notions and topological Krull dimension, but no exact algebraic-space interface.

Validation: all three modules compiled separately through `scompile.py` against
the published live build, in dependency order, with no errors or unexpected
warnings. Only the main theorem is postponed. The first delivery preflight required
the standard empty `import_flags` field on both new nodes; this was added. The first compile exposed a name
collision with the algebraic-space module-pullback functor; every categorical
pullback and its projections are now explicitly qualified with `Limits`.

## New nodes

`def-sfb-algebraic-space-groupoid`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`, defines the groupoid-law predicate
`IsPresheafGroupoid` and the actual canonical pullback `groupoidStabilizer`.
Its source is `spaces-groupoids.tex`, definition-groupoid with its following
paragraph and definition-stabilizer-groupoid, specialized to B = S. The general
presheaf formulas are the underlying formulas for algebraic spaces. The existing
`def-a1-scheme-groupoid-laws` and `def-a1-groupoid-scheme` signatures require
schemes, so cannot take an arbitrary algebraic-space arrow object R. Mathlib
ordinary categorical groupoids do not specify the given source, target, identity,
inverse and composition natural transformations. The new predicate explicitly
checks their laws on every test scheme. It has real Prop-valued data and no sorry;
the stabilizer has real categorical-pullback data and no theorem obligation.

`def-sfb-algebraic-space-etale-dimension`, module
`Sheaf.AlgebraicGeometry.AlgebraicSpaceEtaleDimension`, defines
`etaleLocalDimension` and `etaleDimension`. Its source is `spaces-properties.tex`,
definition-dimension-at-point and definition-dimension. It reuses the existing
field-valued point classes, scheme-point maps, representable-étale predicate and
`topologicalKrullDimAt`. Supremum over all charts through a point is a concrete
construction of the common local value; chart existence and invariance for spaces
are exactly the facts stated before and in the source definition. No such facts
are added as hypotheses of the item, and no choice from a postponed existence
theorem is made. The global definition then takes exactly the pointwise supremum
in the item. Existing definitions are only for topological spaces or schemes;
dimension of the topology of an algebraic space is explicitly a different notion
in the warning immediately following the source definition. The nearby chart
theorem computes stalk dimension, another distinct notion. Searches for both new
nodes and their distinction from existing nodes are recorded in the node files.

## Second reading by NC

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
