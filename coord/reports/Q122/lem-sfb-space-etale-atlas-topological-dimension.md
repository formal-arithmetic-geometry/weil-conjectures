## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceEtaleAtlasTopologicalDimension` states
`AlgebraicGeometry.AlgebraicSpace.space_etale_atlas_topological_dimension` with proof
`sorry`.  It uses the existing `AlgebraicSpace` encoding, `schemeSpace` for a scheme
as an algebraic space, and `enlargedFibreProduct` for the canonical sheaf fibre product.
The base-change scheme `T : Over B` maps to the terminal object of `Over B` through
`Over.homMk T.hom rfl`. The independent atlas scheme is `U : Over B`, and its
representable presheaf is `yoneda.obj U`.

The hypotheses and conclusion are rendered as follows.  `B : Scheme.{u}` and
`X : AlgebraicSpace B` are the base scheme and algebraic space.  The map
`f : X ⟶ schemeSpace (Over.mk (𝟙 B))` is the morphism to the base scheme.  The
quasi-separated hypothesis is
`IsRepresentableWith (fun _ _ p ↦ QuasiCompact p.left)
(Limits.pullback.diagonal f.hom.hom)`, which says on every scheme test that the
representing diagonal morphism is quasi-compact.  `T : Over B` is an arbitrary
scheme over the base.  The displayed `enlargedFibreProduct` is exactly
`X_T = X ×_B T`, formed with the canonical map from `schemeSpace T` to the
base. `U : Over B` is an independent scheme, and
`a : yoneda.obj U ⟶ X_T.obj.obj` is the scheme atlas map. `hae` and
`has` state respectively that it is representable étale and representable
surjective.  The conclusion is equality of `topologicalKrullDim` on the point
space `Point X_T.obj.obj` (whose topology is the final atlas topology supplied
by `pointTopologicalSpace`) and on the underlying atlas scheme `U.left`.  Thus the
empty case is included by `topologicalKrullDim`'s bottom value, and no
finite-type, quasi-compactness, connectedness, or equidimensionality hypothesis
is added.

The statement dependencies used are:

* `def-pc-scheme`: `AlgebraicGeometry.Scheme` from Mathlib.
* `def-trf-algebraic-space`: `AlgebraicGeometry.AlgebraicSpace` and its
  `IsRepresentableWith`, `IsEtale`, and `IsSurjective` predicates from
  `Sheaf.AlgebraicGeometry.AlgebraicSpace`.
* `def-weil-size-convention`: universe parameter `u` is explicit; this is the
  recorded metatheoretic convention and has no Lean declaration.
* `lem-trf-space-fibre-products-etale-covers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`, used by the
  existing `enlargedFibreProduct` construction in
  `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`.
* `def-a1-space-point-topology`:
  `AlgebraicGeometry.AlgebraicSpace.pointTopologicalSpace` from
  `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`.
* `def-kun-topological-krull-dimension`: Mathlib `topologicalKrullDim`.

The existing helper `schemeSpace` and its theorem
`schemeSheaf_isAlgebraicSpace` are imported from
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`; they are the canonical
representable-scheme algebraic-space encoding needed to make the base-change
object, rather than a private replacement.  The proof dependencies
`lem-pc-quasi-compact-base-change`, `lem-sfb-space-topological-dimension-local-rings`,
`lem-pc-scheme-dimension-local-rings`, and `lem-a1-space-point-open-calculus` are
statement-only prerequisites in the DAG and have no usable landed Lean modules
in this checkout, so no proof-only import is made in this statement module.

Edge cases checked: `topologicalKrullDim` uses `WithBot ℕ∞`, so empty point
spaces have bottom dimension; the statement permits an empty atlas exactly when
the surjectivity predicate permits an empty target, and it imposes no finiteness
or boundedness condition, so infinite dimensions remain represented by `⊤`.
`T` and `U` are independent and arbitrary (including non-quasi-separated schemes),
and `u` is the same
universe as the algebraic-space site and its point type.

Searches made before writing:

* `msearch.py ... leanfinder "Topological Krull dimension of a quasi-separated
  algebraic space equals dimension of a surjective etale scheme atlas after any
  scheme base change"`: only scheme, spectrum, and ring dimension declarations;
  no algebraic-space comparison.
* `msearch.py ... loogle "AlgebraicSpace, Etale, topologicalKrullDim"`: zero hits.
* `msearch.py ... grep "AlgebraicSpace|algebraic space|decent" Mathlib/AlgebraicGeometry`:
  zero relevant hits.
* `rg` over `lean/WeilConjectures` and `lean/Sheaf` for the item name and
  atlas/topological-dimension declarations: no existing declaration of this
  theorem; the only relevant declarations were the recorded dependency modules
  and the canonical `schemeSpace`/`enlargedFibreProduct` helpers.

The mathematical DAG statement is unchanged. The returned Lean binder error is
repaired below; no `STATEMENT-DISPUTED` flag applies.

## Second reading by Q122

I reread the node and its source place (Stacks Tags 0A4J, 0A4H, 0BAN, 04N5,
04N6, and 03KL).  The Lean binders match the base scheme, algebraic space,
quasi-separated diagonal, arbitrary scheme base change, representable scheme
atlas `U : Over B`, independent of `T`, and its étale and surjective clauses one by one.  The conclusion uses the
atlas point topology and topological Krull dimension on both sides.  The
canonical pullback and scheme-space maps are explicit, and no finite-type,
quasi-compactness of the atlas, connectedness, or equidimensionality condition
was inserted.  Empty and unbounded-dimensional cases are retained by the
`WithBot ℕ∞` codomain.

## Repair of return on 265f93a44b4b

H3: the returned declaration incorrectly forced the atlas source to equal the
base-change scheme. Added the independent binder `U : Over B`, changed the atlas
to `a : yoneda.obj U ⟶ X_T.obj.obj`, and changed the right-hand side to
`topologicalKrullDim U.left`. The construction of `X_T` still uses `T` alone.
Updated the declaration docstring, the verbatim `lean.statement`, and every
affected clause of this report. Compared the sandbox node with current main
and retained current non-Lean metadata. The original DAG statement needs no
correction: this restores its independent scheme `U`. In particular, a disjoint
union of two copies of a scheme may serve as an atlas without being identified
with `T`; no equality or map between `U` and `T` is assumed beyond the atlas.
