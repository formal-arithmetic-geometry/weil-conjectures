## Worker report

The module `Sheaf.AlgebraicGeometry.SeparablePointCore` states all clauses of
`lem-sfb-separable-point-scheme-core`. Seven theorem proofs are `sorry`; no theorem
is proved. Four canonical helper definitions have actual data. No statement
correction, disputed statement, dependency repair, or new definition node is needed.

The source was read at https://math.stanford.edu/~conrad/papers/cosetfinite.pdf,
PDF page 16, printed p. 15, Lemma 3.1.1. Its assertion is for schemes locally of
finite type; the node intentionally concerns finite-type schemes. The source
asserts the general separable-field point property, functoriality, products and
separable base change, and the group consequence. The node's proof supplies the
explicit closure construction used here. No smoothness conclusion beyond the
node's geometrically reduced group assertion is added.

`separablePointCoreIdeal X` is Mathlib's `vanishingIdeal` of the closed subset
obtained by closing the images of all `SeparableClosure k`-valued k-points of X.
`separablePointCore X` is the `Over` object associated to its `subschemeι` followed
by `X.hom`, and `separablePointCoreι X` is that inclusion over k. These are the
construction in proof step 2, not a choice of arbitrary data from an existence
claim. `separablePointCoreMap f` uses `Classical.choose` on the unique-factorization
theorem, whose equation determines the morphism uniquely.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| k is an arbitrary field | `{k : Type u} [Field k]` |
| X is a k-scheme | `X : Over (Spec (.of k))` |
| X is finite type over k | `[LocallyOfFiniteType X.hom] [QuasiCompact X.hom]` |
| A closed subscheme of X exists | The explicit ideal, its `subscheme`, and `separablePointCoreι`; `separablePointCore_spec` asserts `IsClosedImmersion` of its underlying morphism |
| The subscheme is geometrically reduced | `GeometricallyReduced (separablePointCore X).hom` in `separablePointCore_spec` |
| Every separable L/k, including transcendental ones | `∀ (L : Type u) [Field L] [Algebra k L], Algebra.IsSeparableExtension k L → ...` |
| X(L) is Hom over k | Morphisms from `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k L)))` in `Over (Spec (.of k))` |
| Equality of L-valued points under inclusion | `Function.Bijective (fun t ↦ t ≫ separablePointCoreι X)` |
| Unique geometrically reduced closed subscheme with this property | The final universal clause of `separablePointCore_spec`: any ideal I with geometric reducedness and the same point property equals `separablePointCoreIdeal X` |
| Any k-morphism between finite-type schemes restricts uniquely | `existsUnique_separablePointCoreMap f`, with both schemes' finite-type hypotheses and `∃! g`, satisfying `g ≫ ι Y = ι X ≫ f` |
| Functoriality, identities, composition | `separablePointCoreMap_laws`, including the factorization equation, `map (𝟙 X) = 𝟙 _`, and `map (f ≫ g) = map f ≫ map g` |
| Finite products over k | `separablePointCore_finiteProduct`, for `J : Type u` with `[Finite J]` and a finite-type family X, equates the product's core ideal with `⨆ j, (coreIdeal (X j)).comap (Pi.π X j).left` |
| Products as closed subschemes | The sum of pulled-back ideals cuts out the product of the closed subschemes. Equality of these ideals is equality in the ambient product, and retains the projections |
| Nullary product | The same finite-product statement permits empty J; the supremum is the zero ideal and the product is Spec k |
| Every separable K/k | `separablePointCore_baseChange`, with `[Algebra k K]` and `hK : Algebra.IsSeparableExtension k K` |
| Base change as closed subschemes | `Over.pullback` computes X_K; the core ideal there equals `(separablePointCoreIdeal X).comap (pullback.fst ...)`, precisely the ideal defining the base change of the closed subscheme |
| Geometrically reduced X is its own core | `separablePointCoreIdeal_eq_bot` assumes `[GeometricallyReduced X.hom]` and concludes that the ideal is zero |
| Affine group scheme G | `separablePointCore_closedSubgroup` has `[IsAffine G.left] [GrpObj G]`, and the same finite-type hypotheses |
| Structure maps restrict to a closed subgroup structure | The theorem supplies `∃ s : GrpObj (separablePointCore G), @IsClosedSubgroupScheme ... s ... (separablePointCoreι G)`; that class includes multiplication compatibility and injectivity on all algebra-valued points. Group-hom compatibility also forces compatibility with unit and inverse |
| Geometrically reduced closed subgroup | The group theorem supplies the closed subgroup and affineness; `separablePointCore_spec` supplies geometric reducedness for this same underlying core |
| Empty X, no perfectness/reducedness/smoothness assumption | No `Nonempty`, `PerfectField`, `IsReduced X`, `Smooth`, separatedness, or affineness hypothesis occurs in the general statements |

All fields and schemes use the standard common universe u, as the recorded
scheme and geometric-reducedness interfaces do. Field-extension quantifiers are
in the scheme universe, not in an independent smaller universe. No algebraicity
or finite degree is required of L/k or K/k.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field`, in `Mathlib.Algebra.Field.Defs`.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-weil-finite-type-morphism`: `LocallyOfFiniteType` in
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `QuasiCompact` in
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `def-weil-closed-immersion`: `IsClosedImmersion`, in
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`.
- `def-pc-field-extension`: `Algebra` and `algebraMap`, in
  `Mathlib.Algebra.Algebra.Defs`; scheme maps use `Spec.map`.
- `def-pc-base-change`: the recorded
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` explicitly identifies
  scheme base change with `Over.pullback`, underlying `pullback`, and projections.
  Its module-pullback declaration is not mistaken for scheme base change.
- `def-pc-geometrically-irreducible`: its recorded module
  `Mathlib.AlgebraicGeometry.Geometrically.Integral` publicly provides
  `GeometricallyReduced` from `Mathlib.AlgebraicGeometry.Geometrically.Reduced`;
  the geometric-reducedness clause is the one used here.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` in
  `Mathlib.CategoryTheory.Monoidal.Grp`.
- `def-sc-group-scheme-subgroup`: `IsClosedSubgroupScheme`, in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`. Its full dependent class
  signature and docstring were read; the theorem supplies the source group
  instance explicitly and uses the given target group structure.
- Added the already landed `def-weil-pbc-separable-field-extension` to stmt_deps:
  `Algebra.IsSeparableExtension` in `WeilConjectures.FieldTheory.SeparableExtension`.
  Its definition quantifies over every finitely generated intermediate field and
  requires `IsSeparablyGenerated`; that in turn uses a transcendence basis and
  algebraic separability. This is the precise general notion in the node.

Mathlib's existing `Scheme.IdealSheafData.vanishingIdeal`, `subscheme`,
`subschemeι`, and `comap` provide the closed-subscheme operations; there is no
second definition of any of them. The recorded reduced-induced-closed-subscheme,
reduced-source factorization, smooth-at-generic-point, dense-separable-points,
dense-smooth-locus, and reduced-tensor-product modules are imported as proof
prerequisites. The universal-density and general separable-transitivity proof
nodes currently have no recorded Lean declaration, so there is no corresponding
module to import. They are proof dependencies, not missing notions in this
statement; no duplicate prerequisite statement is introduced.

Edge cases checked before writing and again against the completed signatures:

- Empty X: the set of separable-closure point images is empty, its closure is
  empty, and the vanishing ideal is the unit ideal, giving the empty core.
- Empty finite-product index: the ideal supremum is zero, giving all of Spec k.
- Nonreduced X, e.g. dual numbers over k: the construction cuts out the reduced
  point; the statement does not impose reducedness on X.
- An imperfect field and the spectrum of a proper finite purely inseparable
  extension: no separable-closure points exist, so the core is empty. No claim is
  made that ordinary reduction is geometrically reduced.
- Transcendental separable extensions are allowed by the exact general
  separability predicate; no use of `Algebra.IsSeparable k L` replaces it.
- The identity extension and already geometrically reduced X are covered.
- Nonaffine/nonseparated finite-type schemes remain allowed in all general
  clauses; only the group's explicitly affine clause assumes affineness.

Searches made before constructing a new module:

- `msearch.py leanfinder`: "Every finite type scheme over a field has a unique
  geometrically reduced closed subscheme with the same points over every
  separable field extension". Eight hits, including algebraic geometric
  reducedness and scheme reducedness; no separable-point core theorem.
- `msearch.py loogle`: "Algebra.IsSeparable, AlgebraicGeometry.GeometricallyReduced".
  No hits.
- `msearch.py leansearch`: "unique geometrically reduced closed subscheme separable
  points". Eight hits about geometric reducedness and reduced-source morphism
  equality; none states this theorem.
- `msearch.py grep` in Mathlib AlgebraicGeometry:
  `separable.*(core|subscheme)|separablePoint|separableCore|SeparableCore`. No hits.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  for `separablePointCore`, `separablePointCoreIdeal`, `separableCore`,
  `SeparableCore`, `naturalCore`, and the item id: no matching core construction
  or theorem. `separablePoint_stabilizer_open` is unrelated.
- Broader searches for `GeometricallyReduced`, `IsSeparableExtension`, and
  `SeparablyGenerated` found the reused separability and geometry interfaces.
- DAG concept search for a unique geometrically reduced closed subscheme and
  separable-point core found this item and its consumers, rather than an
  independently recorded construction to reuse.

Compilation: the prescribed `scompile.py Q156 lem-sfb-separable-point-scheme-core`
compiled both sandbox and library module modes cleanly (6.8 s and 9.7 s in the
first run). Every variable and the universe are explicitly bound; no diagnostics
or file-local aliases remain. Dry-run and delivery results are recorded below.

## Second reading by Q156

The dispatcher explicitly prohibits starting other agents. This is a separate
self-check with the completed node and module open, not a claim of independent
worker review; the maintainer's independent review remains necessary.

I re-read each clause in the table against the source signatures. In particular,
point equality is through the actual inclusion, uniqueness compares ideal sheaves
in X, product compatibility compares ideals in the ambient product, and base
change compares ideals in the actual pullback. The product statement includes
empty index types and therefore supplies the unit scheme needed for group
restriction. The chosen map's defining equation, identity, and composition are
all stated. The group conclusion uses the recorded closed-subgroup class, rather
than merely asserting an unrelated group structure on the core.

The reading found one import visibility issue: the reduced-induced theorem is a
proof dependency; its import was changed from public to ordinary import. Its
underlying ideal and subscheme constructions are already public through Mathlib's
ideal-sheaf imports. The separability definition is used in public signatures,
so its already landed node is added to stmt_deps and its import remains public.
No mathematical clause was changed or omitted. No statement correction is needed.

Validation result: `deliver2.py Q156 lem-sfb-separable-point-scheme-core --no-push`
printed `OK (dry run): commit 69865e05d81 passes the preflight and compiles; nothing
pushed`. The dry run checked the final module with the corrected proof-import
visibility, the node record, and this report's required sections.
