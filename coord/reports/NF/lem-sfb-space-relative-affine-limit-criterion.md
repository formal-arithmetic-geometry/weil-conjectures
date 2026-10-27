## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceRelativeAffineLimitCriterion` states
`AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_iff_relative_affine_limit_bijective`.
Its only postponed theorem is this statement, with `sorry`; the complete eight-step DAG
proof is in its docstring. The helper `relativeAffineLimitComparison` constructs the actual
canonical map using the colimit universal property, with real data and a direct naturality
check. It makes no choice of an arbitrary map or bijection.

Sources read: `literature/stacks-project/spaces-limits.tex`, Tag 04AK
(`proposition-characterize-locally-finite-presentation`, including the size remark) and
Tag 06BC (`lemma-characterize-relative-limit-preserving`); and
`spaces-morphisms.tex`, Tag 03XP (`definition-locally-finite-presentation`). These assert
exactly the local-finite-presentation / relative cartesian-square equivalence, without
compactness or separation assumptions. No mathematical correction is needed.

Hypothesis and clause correspondence:

- The base scheme is `{S : Scheme.{u}}`. The spaces are `{X Y : AlgebraicSpace S}` and
  the morphism is `(f : X ⟶ Y)`. These are the dependency's fppf sheaves with representable
  diagonal and surjective étale atlas, and their natural transformations.
- Local finite presentation is the existing `MapIsLocallyOfFinitePresentation f`, i.e.
  `MapIsLocally (@LocallyOfFinitePresentation) f`. This is the all-compatible-étale-chart
  predicate in the landed node `def-sfb-space-morphism-properties`, added to `stmt_deps`
  under the permission in brief-stage2 §5 to add already-landed nodes. It is exactly the
  node's stated surjective pullback-chart test: the read theorem
  `local_properties_chart_test` with P = `@LocallyOfFinitePresentation` identifies it
  with local finite presentation of the canonical map `W → V` for any pair of the
  specified surjective étale charts. Such pairs exist by the atlas and sheaf-fibre-product
  interfaces. Thus universal quantification over those pairs recovers the same predicate.
  This uses the established notion rather than defining a duplicate.
- Small nonempty directed sets are `(I : Type u) [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`. This follows the standing directed-set and index
  universe conventions; antisymmetry is not imposed.
- The inverse system of S-schemes is `(D : Iᵒᵖ ⥤ Over S)`; the hypothesis
  `(∀ i : Iᵒᵖ, IsAffine (D.obj i).left)` says every underlying scheme is affine.
  These are arbitrary S-schemes, not required to be finitely presented over S.
- The limit is any `(c : Cone D)` with `IsLimit c`. A limit in `Over S` is precisely
  the scheme limit with its compatible S-structure; `Over.forget S` creates connected
  limits, and a nonempty directed index category is connected. Affine-stage limits exist by the recorded affine-transition theorem and are
  affine; using any supplied limiting cone avoids choosing a privileged presentation.
- The set `Mor_S(T_i,X)` is `X.obj.obj.obj (op (D.obj (op i)))`. The directed functor is
  `D.rightOp ⋙ X.obj.obj`; its maps are the sheaf's precomposition maps.
  The corresponding Y-diagram is `D.rightOp ⋙ Y.obj.obj`.
- The comparison's domain is `colimit (D.rightOp ⋙ X.obj.obj)`. Its codomain is
  `Limits.pullback (f.hom.hom.app (op c.pt)) (colimit.desc ... Y ...)`, formed in
  `Type u`. This is `X(T) ×_{Y(T)} colim Y(T_i)`, in exactly the order in the node.
- The first component is `colimit.desc` of the cocone obtained by applying X to the
  opposite limit projections. The second is `colimMap (Functor.whiskerLeft D.rightOp
  f.hom.hom)`, hence composition with f at each stage. Naturality of f on each
  projection gives the equality needed by `pullback.lift`.
- The two maps into `Y(T)` are respectively the component of f and restriction from
  the Y-colimit. The assertion is `Function.Bijective (relativeAffineLimitComparison
  f D c)` for every such system and cone. Thus it concerns the canonical map, rather
  than existence of some abstract equivalence of sets.
- Neither side has any quasi-compactness or quasi-separatedness binder. There is no
  restriction on the characteristic, on a base field, or on affineness of S, X or Y.

Dependency interfaces read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, and
  `IsAlgebraicSpace`. The full-subcategory and sheaf projections give the presheaf
  and the natural transformation used in the comparison.
- `def-weil-size-convention` is metatheoretic; it has no Lean declaration. Explicit
  universe u, Scheme.{u}, I : Type u, and Type u-valued space presheaves implement it.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation` is the affine-local scheme property.
- `WeilConjectures.AlgebraicGeometry.LimitAffineTransition`:
  `AlgebraicGeometry.exists_limit_affine_transition`, including its affine-stage
  spectrum-of-colimit clause; this supplies the affine systems' limit interface.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `CategoryTheory.Limits.colimit`,
  `colimit.desc`, `colimMap`, and the coprojection equations. The chosen colimits
  exist in sets; no redundant HasColimit assumption is introduced.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocallyOfFinitePresentation` and `MapIsLocally`.
- `Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest`:
  `AlgebraicGeometry.AlgebraicSpace.local_properties_chart_test`, read with its full
  arbitrary-surjective-chart signature and proof docstring, justifies the exact
  chart-predicate correspondence above.

Public imports expose the statement interfaces. The already-stated proof dependencies
are imported without `public`: filtered set colimits; affine transitions; space fibre
products and representable étale scheme tests; scheme permanence and composition;
space chart tests; atlas presentations; the scheme affine limit criterion; fppf
sheafification continuity; and space change of base. The Mathlib permanence and
composition declarations are supplied by the finite-presentation, étale and
quasi-separated imports. There are no unavailable proof dependencies to defer.

Edge cases checked before writing:

- Empty directed index sets are excluded explicitly, as in the node. Singleton and
  constant diagrams are included: their comparison is the usual identity-base-change
  fibre-product identification, imposing no condition on a single stage.
- Empty affine test schemes and empty source/target spaces remain included. Charts
  may be empty; no Nonempty is imposed on a scheme or on its point set.
- Identity f is included: its comparison identifies a colimit class with its restriction
  and the same class. An empty source has both the empty source colimit and empty
  fibre product, consistent with vacuous local finite presentation.
- Infinite directed systems and non-antisymmetric directed preorders are included.
  The index universe matches the scheme and point universes, avoiding a too-small or
  unbounded test universe. No transition affineness assumption is added, since maps
  between affine schemes are affine.
- Non-quasi-compact and non-quasi-separated X, Y and S remain admissible.

Actual searches on 2026-10-24:

- `msearch.py ... leanfinder "A morphism of algebraic spaces is locally of finite
  presentation if and only if the relative comparison on directed limits of affine
  schemes is bijective"`: eight hits, all scheme-level finite-presentation material;
  no algebraic-space relative criterion.
- `msearch.py ... loogle "AlgebraicGeometry.AlgebraicSpace,
  LocallyOfFinitePresentation"`: zero hits, with unknown identifier
  AlgebraicGeometry.AlgebraicSpace reported by the external Mathlib index.
- `msearch.py ... grep "AlgebraicSpace|relativeLimit|relative_limit"
  AlgebraicGeometry`: zero hits in Mathlib.
- `msearch.py ... leansearch "relative limit preserving morphism of algebraic spaces
  and local finite presentation"`: eight scheme-level hits; no relative-space theorem.
- Local `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for affine limit
  bijectivity, relative limits and MapIsLocally found the scheme affine limit theorem
  and the existing chart predicate. Their full source and docstrings were read.
  The source search by the item id returned no declaration. Exact-name searches for
  both proposed names in Mathlib's source index / `dag/lean_names_upstream.json`,
  `lean/WeilConjectures`, and `lean/Sheaf` found no existing declaration.

No new nodes, dependency modules, statement correction or STATEMENT-DISPUTED fault.
The only node changes are its Lean record and the added landed definition dependency.

## Second reading by NF

A second manual pass by this worker compared the node, its Stacks sources, the full
chart-test theorem and the delivered file. No independent agent was started, as the
dispatcher brief requires. The maintainer performs the independent review.

The base scheme and space morphism have precisely the dependency types. The existing
MapIsLocallyOfFinitePresentation predicate agrees with every surjective pullback-chart
condition by the recorded chart-test theorem, so replacing it by an ad hoc second
predicate would be unnecessary. The new dependency edge records this actual reuse.
The right side quantifies over all and only the specified directed affine systems,
with a genuine scheme limit over S. Reading the comparison definition shows that the
X-component restricts to T and the Y-component composes with f before taking the
colimit class; its pullback legs are exactly the two maps stated in the node.
The compatibility proof is naturality, not an assumption. Function.Bijective retains
both injectivity and surjectivity. No qc, qs, nonempty-space or test-presentation
hypothesis slipped in. All binders and universes are explicit and autoImplicit is off.
The theorem's eight proof steps match the DAG. No mathematical mismatch was found;
compile feedback corrected only Mathlib API spelling and simp normalization in the
canonical-map definition.

Validation: the prescribed scompile.py wrapper compiled both its sandbox probe and the
actual library module cleanly (3.2 s and 1.8 s), with no errors or extra warnings.
