## Worker report

The module `Sheaf.AlgebraicTopology.BoundaryProperFaceLimit` states
`SSet.boundary_proper_face_limit`, with `sorry` as its only theorem proof, and defines the
actual coordinate evaluation `SSet.boundaryProperFaceEvaluation` with real data. No
statement correction, disputed claim, new node, or dependency repair was needed.

The statement matches each hypothesis and clause as follows:

- A small simplicial set is `T : SSet.{u}`, Mathlib's functor
  `SimplexCategoryᵒᵖ ⥤ Type u`; every universe is explicitly bound. The theorem quantifies
  over all such `T`, so one equivalence family `E` handles naturality in the target.
- `n : ℕ` includes every `n ≥ 0`. No positive-degree hypothesis is imposed.
- The standard simplex is Mathlib's `SSet.stdSimplex.obj ⦋n⦌`, whose degreewise
  `stdSimplex.objEquiv` identifies its simplices with order-preserving maps. Mathlib's
  `boundary n` is literally the subfunctor of nonsurjective maps, with precomposition
  operators, and its `toSSet` is used as the source of the Hom set.
- Proper injections are the existing `ProperFaceCategory n`: an object `a` consists of
  an over-object `a.obj.hom : a.obj.left ⟶ ⦋n⦌` with `a.property.1 : a.obj.left.len < n`
  and `a.property.2 : Function.Injective a.obj.hom.toOrderHom`.
- The existing `properFaceDiagram T n` uses the opposite proper-face category, giving
  exactly the arrows `T_k → T_l` for `theta : [l] → [k]` with `theta ≫ iota = iota'`.
  Every such triangle map is injective: injectivity of `theta ≫ iota = iota'` implies
  injectivity of `theta`. Conversely every injective theta in the node gives this arrow.
  Thus it imposes precisely the stated compatibilities, without extra conditions.
- The set `F_n(T)` is expressed by
  `(Functor.const (ProperFaceCategory n)ᵒᵖ).obj PUnit.{u+1} ⟶ properFaceDiagram T n`.
  A component is a function from a singleton into `T_k`, hence exactly an element
  `x_iota`. Naturality of this transformation is exactly `T(theta) x_iota = x_(iota theta)`.
  This reuses the category-theoretic compatible-family definition rather than introducing
  a second family structure or a second proper-face index.
- `E T` is an equivalence between the actual boundary Hom set and that family set.
  Its first conjunct requires `(E T h).app (op a) PUnit.unit` to equal the explicit
  `boundaryProperFaceEvaluation h a`. The helper evaluates `h` on
  `stdSimplex.objEquiv.symm a.obj.hom`; boundary membership follows from the existing
  `boundary_obj_eq_univ` theorem in degree less than `n`. This formula uniquely determines
  the equivalence's forward map at every coordinate; it is the restriction map in the node.
- The second conjunct is naturality in every morphism `u : T ⟶ T'`, at every coordinate:
  evaluation of `E T' (h ≫ u)` equals application of `u.app` to evaluation of `E T h`.
  Equality on all singleton components is equality of the associated natural transformations,
  so this is the full naturality square for the componentwise map on families.
- The third conjunct uses `(boundary n).ι ≫ yonedaEquiv.symm z` for the boundary
  restriction of the map represented by `z : T.obj (op ⦋n⦌)`. Its coordinate is required
  to be `T.map a.obj.hom.op z`, exactly the final displayed formula of the node.
- The fourth conjunct provides a cone `π` on the existing diagram whose apex is literally
  `((boundary n).toSSet ⟶ T)`. Every projection is required to be the same explicit
  evaluation, and `Nonempty (IsLimit (Cone.mk _ π))` asserts the full categorical limit
  universal property in sets, including all test sets and cone maps.
- The final conjunct, when `n = 0`, gives `∃!` for both a boundary map and a compatible
  family. These mean exactly that both sets are singletons. The predicate `True` here
  asserts uniqueness of an element, not an added hypothesis.

Dependencies read and reused:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf with no `lean` record. Its match consists
  of `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`, `SSet.degenerate` and
  `SSet.nonDegenerate` in `.Degenerate`, `SSet.Subcomplex` in `.Subcomplex`, and
  `SSet.Finite` in `.Finite`. Their full signatures and docstrings were read. Only the
  simplicial-set and subcomplex portions occur in this statement.
- Added the already landed `lem-weil-pbc-matching-object-proper-faces` to `stmt_deps`,
  importing `Sheaf.CategoryTheory.ProperFaceMatchingObject`. Reused its helper declarations
  `CategoryTheory.SimplicialObject.properFaceProperty`, `ProperFaceCategory`, and
  `properFaceDiagram`, after reading the complete source and the owning node's statement
  and Lean record. No changes to that node or its module were made.
- `Mathlib.AlgebraicTopology.SimplicialSet.Boundary` supplies `SSet.boundary`,
  `boundary_obj_eq_univ`, the inclusion, `stdSimplex.objEquiv`, and `yonedaEquiv`.
- The proof dependencies `lem-weil-pbc-simplex-face-factorization` and
  `lem-weil-pbc-simplex-face-face-identity` are Mathlib leaves. Read the actual signatures
  of `SimplexCategory.eq_comp_δ_of_not_surjective'`, the `Mono (δ i)` instance,
  `Function.Injective.of_comp`, and `SimplexCategory.δ_comp_δ`. Their source module
  `Mathlib.AlgebraicTopology.SimplexCategory.Basic` is already imported transitively
  by Boundary; no duplicate import is needed. The theorem docstring records all eight
  proof steps, including choice independence and degeneracy naturality.

Edge cases checked before writing: `n = 0` has no proper faces and an empty boundary,
so both sets are singletons even for empty `T`; `n = 1` gives two independent vertices;
`n = 2` gives the usual three edges with vertex compatibility. If `T` is empty and
`n > 0`, both sets are empty because there are vertices. Arbitrarily high-degree
boundary simplices remain in the Hom set; their reconstruction uses all simplicial
operators, not just injections. The singleton is explicitly in `Type u`, and no size
restriction beyond the simplicial set's own universe is imposed.

Source verification: read the whole omitted-vertex reconstruction in local Stacks
`simplicial.tex`, `lemma-formula-limit` (Tag 0186), including independence, arbitrary
operators, inverse constructions, and functoriality. The node's boundary and Yoneda
notions agree with the Mathlib definitions and their source docstrings. This calculation
is a child of the blueprint unit, not a change to the unit statement.

Searches for an existing declaration (2026-10-17):

- `msearch.py leanfinder`, query: "Maps from a simplex boundary to a simplicial set are
  compatible families on all proper injective faces". Eight hits, including `SSet.boundary`,
  horn maps, and pointed-simplex relative structures; none states the comparison.
- `msearch.py loogle`, query `SSet.boundary`: twelve hits, including its definition,
  `boundary_obj_eq_univ`, face inclusions, and zero-dimensional Hom extensionality;
  none gives the comparison or limit cone.
- `msearch.py grep`, query
  `boundary.*([Ee]quiv|[Ll]imit)|([Ee]quiv|[Ll]imit).*boundary|properFaceFamily`,
  subdirectory `AlgebraicTopology`: no hits.
- `msearch.py loogle`, query `SSet.yonedaEquiv`: found the canonical standard-simplex
  Yoneda equivalence and its component formulas; reused this rather than constructing
  a second simplex correspondence.
- `rg` of `properFaceFamily`, boundary/compatible and boundary/matching patterns over
  the source project's `WeilConjectures` and this project's `lean/Sheaf` found the parent
  `BisimplicialReedyDivisionCalculus` proof, the different semi-representable Hom theorem,
  and `ProperFaceMatchingObject`. The latter's existing index/diagram is reused; its
  theorems compare codimension-one tuples in a general category, not boundary Hom sets.
  An initial topic-directory search found no upstream `AlgebraicTopology` directory;
  the corrected search covered the whole `WeilConjectures` source tree.
- Direct node-id search over upstream `WeilConjectures` found no declaration for the item.
  Exact proposed names `boundary_proper_face_limit` and `boundaryProperFaceEvaluation`
  had no hits in Mathlib, upstream, or this project's Lean before writing.

Validation: `scompile.py Q82 lem-coef-boundary-proper-face-limit` compiled the delivered
file in both the isolated sandbox and library contexts with no errors or warnings
(1.5 seconds and 1.6 seconds respectively). The only postponed result is the named
main theorem; the evaluation definition contains no `sorry` or choices.

## Second reading by Q82

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
