## Worker report

The module `Sheaf.AlgebraicGeometry.StackRelativeDiagonalFiniteType` states
`CategoryTheory.moduliRelativeDiagonal_locallyOfFiniteType`, with `sorry` as its
only proof. No definitions or auxiliary theorems are introduced. The statement
of the DAG node is unchanged. Its `stmt_deps` additionally cites the landed
`def-sfb-dm-stack-morphism-properties`, which owns both existing constructions
used in the conclusion. No dependency node is modified.

Source read: `literature/stacks-project/stacks-morphisms.tex`,
`lemma-properties-diagonal` (Tag 04XS), lines 130–189, including the fibre square
`equation-diagonal` (04XT). Both conclusions are exactly those of this source.
The theorem docstring gives the node's four proof steps, including the explicit
isomorphism-space fibre and the equivalence preserving the projection to T.

Clause-by-clause correspondence:

- The scheme S is the binder `{S : Scheme.{u}}`. The size convention is expressed
  by explicit universe levels `u v₁ w₁ v₂ w₂`; the source and target stack
  categories have independent morphism and object universes. There are no
  auto-bound variables (`set_option autoImplicit false`).
- The algebraic stacks over S are
  `{X : BasedCategory.{v₁, w₁} (Over S)}` and
  `{Y : BasedCategory.{v₂, w₂} (Over S)}`, with precisely
  `hX : IsAlgebraicModuliStack X` and `hY : IsAlgebraicModuliStack Y`.
  This predicate requires étale stack descent, algebraic-space diagonal, and a
  smooth surjective scheme atlas. Neither stack is required to be DM.
- The arbitrary morphism is `f : BasedFunctor X Y`. No representability,
  finite-type, quasi-compactness, or separation condition is imposed on f.
- The exact canonical relative diagonal is `moduliRelativeDiagonal f`.
  Its real definition sends x to `(x,x,𝟙 (f.obj x))` and arrows a to `(a,a)`
  in `moduliTwoFiberProduct f f`, rather than selecting an unrelated map.
- The single conclusion is
  `ModuliSpaceTest @LocallyOfFiniteType (moduliRelativeDiagonal f)`.
  Unfolding the already recorded `ModuliSpaceTest` quantifies over every
  `T : Over S` and every
  `t : BasedFunctor (discreteModuli (yoneda.obj T))
    (moduliTwoFiberProduct f f)`.
  Thus these are exactly all scheme maps to the relative self-product.
- For each test it asserts an algebraic space `Z : AlgebraicSpace S` and a map
  `p : Z.obj.obj ⟶ yoneda.obj T`, together with
  `HasSpaceBaseChange (moduliRelativeDiagonal f) T t Z p`.
  This last predicate supplies a based functor from the discrete fibred
  groupoid of Z to the specified two-fibre product, an equivalence of total
  categories, and a vertical natural isomorphism comparing its first projection
  with `discreteModuliMap p`. This is the required equivalence over T, retaining
  the projection. Forgetting the chart condition gives precisely
  `IsRepresentableByAlgebraicSpaces (moduliRelativeDiagonal f)`.
- For every `U : Over S`, `a : yoneda.obj U ⟶ Z.obj.obj`, and
  `AlgebraicSpace.IsEtale a`, the conclusion requires
  `LocallyOfFiniteType (yoneda.preimage (a ≫ p)).left`. This is ordinary scheme
  local finite type on every étale chart of the represented space over T.
  It is exactly the algebraic-space local-finite-type assertion in the node,
  and does not assert quasi-compactness or finite type. Scheme targets can be
  tested on the identity target chart; further étale target charts give the
  equivalent compatible-chart formulation by scheme base change.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom` (structure signatures and docstrings).
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`:
  `CategoryTheory.IsAlgebraicModuliStack`, and its smooth-atlas predicate.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `HasSpaceBaseChange`,
  `IsRepresentableByAlgebraicSpaces`, and the stack/diagonal predicates.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `IsAlgebraicSpace`, `IsEtale`, and
  `IsRepresentableWith`. The algebraic spaces are the existing full
  subcategory of fppf sheaves, not a replacement category.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.moduliRelativeDiagonal` and `CategoryTheory.ModuliSpaceTest`.
  Despite the module name, both declarations quantify over arbitrary based
  categories; they require no DM hypothesis. This is the added landed node.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType` (all-affine-pairs ring-map definition).
- The already stated proof dependency
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers` is imported
  privately; its `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`
  supplies the space fibre product. The current node records of
  `lem-sfb-stack-isom-space-locally-finite-type`,
  `lem-sfb-space-lft-cancellation`, and `lem-sfb-stack-finite-type-calculus`
  have no Lean module yet; they cannot be imported. They remain cited in the
  full proof docstring and are unchanged. None is needed to type the statement.

Edge cases checked mathematically: for f the identity, every diagonal test is
T up to equivalence, so the identity scheme projection is locally of finite
type. If α has no lift in the Isom map, the test space is empty, which is
permitted. Empty S, empty X, and an empty test T impose no nonemptiness
hypothesis. Nonrepresentable f and non-DM algebraic stacks (for example maps
involving BG_m) are included: the conclusion concerns their relative diagonal,
not f itself. No quasi-compactness of its fibres is asserted. Nonreduced test
schemes and all characteristics are included. Independent universe levels are
retained and every S-scheme in the fixed scheme universe is tested.

Searches actually run on 2026-10-24:

- `msearch.py ... leanfinder` with query “The relative diagonal of any morphism
  of algebraic stacks is representable by algebraic spaces and locally of
  finite type”: eight hits, all scheme diagonal or affine-target morphism
  properties; no algebraic-stack theorem.
- `msearch.py ... loogle` with query `"LocallyOfFiniteType", "diagonal"`:
  zero hits.
- `msearch.py ... leansearch` with query “For any morphism of algebraic stacks
  the relative diagonal is representable by algebraic spaces and locally of
  finite type”: eight hits, concerning scheme diagonals or ordinary functor
  representability, not the requested stack theorem.
- `msearch.py ... grep` with query
  `AlgebraicStack|diagonal.*LocallyOfFiniteType|LocallyOfFiniteType.*diagonal`:
  one Mathlib hit in `Morphisms/FormallyUnramified.lean`, a scheme result.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `AlgebraicStack|relativeDiagonal|relative_diagonal|` followed by the item id
  found no existing statement of this theorem. Further searches for
  `moduliRelativeDiagonal`, `ModuliSpaceTest`, chartwise finite-type terms,
  and `moduliRelativeDiagonal_locallyOfFiniteType` found the reusable
  definitions above and a general chart criterion, but no existing theorem
  asserting the relative-diagonal conclusion. The intended new full name is
  absent from Mathlib/project sources and `dag/lean_names_upstream.json`.

Validation: the prescribed `scompile.py` compiled the delivered file in both
sandbox and library contexts on the live server (3.6 s and 4.0 s), with no errors
or warnings. No statement dispute, hollow definition, new node, or source
correction was needed. The maintainer supplies the independent review.

## Second reading by O2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
