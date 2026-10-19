## Worker report

The module `Sheaf.AlgebraicGeometry.SeparatedEtaleSpaceScheme` states
`AlgebraicGeometry.AlgebraicSpace.exists_scheme_of_separated_etale`, with the
single expected `sorry` proof. No definition, helper, dependency repair, or node
statement change is needed.

Clause-by-clause correspondence:

- The scheme `X` is `{X : Scheme.{u}}`, with the universe explicitly bound.
- The algebraic space over `X` is `(E : AlgebraicSpace X)`, using the dependency's
  full subcategory of fppf sheaves. This includes exactly its representable
  diagonal and existence of a surjective representable étale scheme atlas.
- The map `q : E → X` is its structure morphism: working with presheaves on
  `Over X` encodes that morphism throughout. It is not an extra choice of a map
  to an unrelated base. All Yoneda maps and isomorphisms in the signature are
  on `Sch/X`, so all triangles commute over the stated base.
- Every scheme over `X` is quantified by `V : Over X`, and every scheme-chart
  map by `a : yoneda.obj V ⟶ E.obj.obj`. The dependency's `IsEtale a` includes
  representability and étaleness after every scheme base change. The implication
  `IsEtale a → Etale V.hom` in `het` says precisely that the composite to `X`
  is étale. Surjectivity of an individual chart is not assumed.
- The diagonal `E → E ×_X E` is
  `prod.lift (𝟙 E.obj.obj) (𝟙 E.obj.obj)`. Because the presheaves are on
  `Sch/X`, their product is the relative product over `X`. This is also the
  dependency's exact diagonal expression, with no second definition.
- The hypothesis `hsep` applies the dependency's `IsRepresentableWith` to this
  diagonal and the scheme-morphism property
  `fun _ _ p ↦ IsClosedImmersion p.left`. Unfolding that predicate quantifies
  over every scheme `T` over `X` and map `h_T → E ×_X E`, and requires an actual
  scheme pullback square whose projection is a closed immersion. This is the
  node's testwise closed-immersion condition, not scheme separatedness applied
  to a nonexistent scheme model of `E`.
- The conclusion quantifies `∃ Z : Over X`, so it supplies both the representing
  scheme and its morphism to `X`. `Nonempty (yoneda.obj Z ≅ E.obj.obj)` says its
  functor of points is isomorphic to `E` over `X`. As both sides are sheaves,
  this presheaf isomorphism is equally an isomorphism of algebraic spaces. The
  conjunct `Etale Z.hom` is precisely étaleness of the representing structure map.
- There is no quasi-compactness, quasi-separatedness, finite-type, base-field,
  Noetherian, or nonemptiness hypothesis. Nothing restricts the size of a
  scheme beyond the universe already used by `AlgebraicSpace.{u}`.

Dependency declarations read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `def-trf-algebraic-space`: `Sheaf.AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicGeometry.AlgebraicSpace`, `AlgebraicSpace.IsRepresentableWith`,
  `AlgebraicSpace.IsEtale`, and `AlgebraicSpace.IsAlgebraicSpace`. Their full
  definitions and docstrings were read, including the scheme-valued pullback
  witnesses in `IsRepresentableWith`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  `AlgebraicGeometry.Etale` (the current spelling, rather than deprecated `IsEtale`).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, its projections and universal property. The
  present relative product is rendered by the categorical product on `Sch/X`
  presheaves, as in the recorded algebraic-space definition.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`.
- The stated proof dependency `def-weil-proper-morphism` is imported privately
  through `Mathlib.AlgebraicGeometry.Morphisms.Proper`; the relevant definition
  is `AlgebraicGeometry.IsSeparated`, whose diagonal clause was read.
- The Mathlib proof leaf `lem-weil-pbc-etale-composition-cancellation` is already
  imported via `Morphisms.Etale`; its open-immersion instance and composition
  instance were read. The other two proof dependencies,
  `lem-a1-etale-space-locally-quasi-finite` and
  `lem-a1-separated-locally-qf-space-representable`, have no Lean record or
  Mathlib match in the available DAG and need no imports yet. They are named
  explicitly in the four-step proof docstring, preserving the node's proof plan.

Source and edge cases checked before writing:

- Read `spaces-morphisms.tex`, `lemma-etale-locally-quasi-finite` (03XU),
  and `proposition-locally-quasi-finite-separated-over-scheme` (03XX). The latter
  assumes a representable target, locally quasi-finite map and separatedness;
  it imposes no quasi-compactness condition. The docstring follows the node's
  route through these two inputs and its final representing chart.
- The empty algebraic space is allowed, represented by the empty scheme, with
  étale empty structure map; the signature does not demand an inhabited chart.
  The empty base likewise remains allowed.
- Arbitrary infinite disjoint unions of copies of a nonempty base are included:
  their maps are étale and separated, without being quasi-compact. No finite
  atlas, finite index type or compact-space instance is hidden in the signature.
- For a represented space, the Yoneda identity/isomorphism is one of the charts
  tested by `het`; its scheme base changes are isomorphisms, so the final
  conclusion is about the same structure morphism.
- Étale morphisms need not be separated. The doubled-origin line over the line
  explains why the diagonal hypothesis is substantive, although the doubled
  line is itself still a scheme. No separation hypothesis is silently inferred
  from étaleness.

Searches for an existing statement (all searches returned no exact match):

- `msearch.py leanfinder`: “A separated etale algebraic space over a scheme is
  represented by a scheme without a quasi compactness assumption”. Eight hits:
  `Scheme.Etale`, `IsSeparated.hasAffineProperty`, `IsEtale`,
  `Scheme.instCategoryEtale`, `Scheme.Etale.forget`, `Scheme.IsSeparated`,
  `Scheme.instIsSeparatedOfIsSeparated`, and an étale cancellation instance.
  These concern schemes, not the asserted algebraic-space representability.
- `msearch.py loogle`: `"AlgebraicSpace", "IsSeparated"`; zero hits.
- `msearch.py grep`: `AlgebraicSpace|separated.*algebraic.space|etale.*space.*scheme`
  in Mathlib `AlgebraicGeometry`; zero hits.
- `msearch.py leansearch`: “A separated etale algebraic space over a scheme is
  represented by a scheme”. Eight hits on `Scheme.Etale`,
  `Algebra.FormallyEtale.of_isSeparable`, `IsEtale`,
  `Scheme.instIsSeparatedOfIsAffine`, `IsSeparated`, `IsSeparated.mk`,
  `Algebra.Etale.formallyEtale`, and `Scheme.IsSeparated`; no exact statement.
- `rg` in upstream `WeilConjectures` and this project's `lean/Sheaf` for
  `AlgebraicSpace`, the node id, separated/étale combinations, and the proposed
  declaration name. Upstream supplies no algebraic-space schemehood statement.
  The side project supplies its algebraic-space interface and other results,
  including `SpaceQCSeparatedEtaleLocal` and `EtaleAffineQuotientRepresentable`,
  whose signatures were read; neither states this theorem. Exact-name/id
  searches have no hit. `dag/lean_names_upstream.json` has no corresponding
  algebraic-space declaration.

No statement dispute or node fault was found. The statement uses only existing
notions and changes only the item's `lean` record.

## Second reading by Q08

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
