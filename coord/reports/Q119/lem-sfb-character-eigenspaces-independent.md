## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CharacterEigenspaces` states
`AlgebraicGeometry.CharacterEigenspaces.independent_and_finite` with `sorry`.
It also gives real constructions of the scalar-extended action, the stated
stability predicate, character evaluation and the character eigenspaces. These
are helper declarations belonging to this node's own definitions, and all are
listed in `lean.declarations`. There are no additional postponed theorems,
dependency repairs, new nodes or statement corrections.

The source was read directly: Milne, Algebraic Groups (2017), printed pp.92--94,
Chapter 4(g), Proposition 4.22, Corollary 4.24 and Theorem 4.25. The theorem's
docstring follows all six steps of the node's proof: coordinate Hopf algebra,
distinct group-like character coordinates, universal-point evaluation,
separation by linear forms, dimension bound for nonzero summands, and the
injective canonical sum map. The finite-support consequence uses finite
dimension; the directness assertion does not assume that the spaces span V.

Hypothesis and clause correspondence:

- The algebraically closed field is `{k : Type u} [Field k] [IsAlgClosed k]`.
- The group scheme is `{G : Over (Spec (.of k))} [GrpObj G]`; affineness is
  `[IsAffine G.left]`. Finite type is precisely `[LocallyOfFiniteType G.hom]`
  and `[QuasiCompact G.hom]`, as specified by the dependency record.
- The finite-dimensional vector space is `{V : Type v} [AddCommGroup V]`
  `[Module k V] [FiniteDimensional k V]`. The chosen basis is
  `(b : Module.Basis n k V)` for arbitrary finite `n : Type u`, with explicit
  `[Fintype n] [DecidableEq n]`. This includes the empty basis. A small finite
  basis can be chosen regardless of the universe of V, which remains independent.
- The representation is `(r : G ⟶ GeneralLinearGroup n k) [IsMonHom r]`.
  The existing scheme `GeneralLinearGroup` and `homMulEquiv` are used directly.
  The action is the actual matrix action on `n → A`, conjugated through
  `(b.baseChange A).equivFun`; its domain and codomain are `A ⊗[k] V`.
- The definition of G-stability is `IsStable b r W`. It says that for every
  commutative k-algebra A and every A-point g, the image of `W.baseChange A`
  under `action b r A g` is contained in `W.baseChange A`.
- Characters are the existing bundled homomorphisms
  `Grp.mk G ⟶ Grp.mk (GeneralLinearGroup (LinearGroupSchemes.Index 1) k)`.
  This is GL_1 as in the node, without introducing a second multiplicative
  group scheme. `characterValue` takes its unique matrix entry under the
  existing canonical point equivalence, so multiplication by this element
  is precisely scalar multiplication by the value of the character.
- The subspace `eigenspace b r χ` is an intersection over every
  `(A : Type u) [CommRing A] [Algebra k A]` and every A-point g of the linear
  equalizer between `v ↦ action b r A g (1 ⊗ v)` and
  `v ↦ characterValue χ A g • (1 ⊗ v)`. `TensorProduct.mk k A V 1` is exactly
  the linear map `v ↦ 1 ⊗ v`. These are actual equalizers, not a span of a
  potentially smaller or larger set. The test universe contains k and k[G],
  hence the universal point; tests in larger universes give the same condition
  by the universal coordinate-algebra map and naturality of matrix entries.
- Independence is `iSupIndep (eigenspace b r)`. Its finite-sum meaning is the
  node's stated relation: Mathlib's
  `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero` identifies it with the assertion
  that a zero sum of vectors in finitely many distinct summands has every term
  zero. A finset of characters encodes their pairwise distinctness.
- Finiteness of the nonzero spaces is
  `Set.Finite {χ | eigenspace b r χ ≠ ⊥}`.
- The internal direct sum conclusion is explicitly
  `Function.Injective (DirectSum.coeLinearMap (eigenspace b r))`.
  Mathlib's `DirectSum.range_coeLinearMap` identifies its image with
  `⨆ χ, eigenspace b r χ`, the sum of all character eigenspaces. Thus this
  exact canonical map identifies the external sum with their internal sum.
  It does not assert that their sum is V. Classical equality on the character
  index is supplied by `open Classical in`, without file-local notation or
  a local instance declaration.
- No commutativity, smoothness, connectedness or characteristic restriction
  is imposed on G or k. G-stability is introduced as a predicate, not required
  as an extra hypothesis on the representation or individual eigenspaces.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`, the algebraically
  closed clause of the recorded algebraic-closure match.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`; and
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`. The terminology agrees
  with `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes`: `LinearGroupSchemes.Index`;
  its public upstream dependency
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear` gives
  `GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`. The recorded GL
  node expressly uses these upstream constructions rather than redefines GL.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct` and
  `TensorProduct.mk`; `Mathlib.LinearAlgebra.TensorProduct.Basis`:
  `Module.Basis.baseChange`; the scalar-extended subspace is the existing
  `Submodule.baseChange` in TensorProduct.Tower.
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`: `FiniteDimensional`.

Already available proof dependencies are imported privately:
`Mathlib.RingTheory.Coalgebra.GroupLike` for independence of group-like
elements, `Mathlib.LinearAlgebra.Basis.VectorSpace` for extension of a linear
form, and `Mathlib.LinearAlgebra.Dimension.Finite` for the dimension bound.
Affine spectra and the coordinate Hopf algebra are already exposed by the
public general-linear-group import. All variables and universes are explicit;
the file disables autoImplicit.

Edge cases checked before writing: V = 0 has the empty basis and GL on the
empty matrix index, the trivial group scheme already supported upstream.
Its tensor extensions are zero, every eigenspace is bottom, and the nonzero
support is empty. Empty finite relations are vacuous. The zero test algebra
is included by `CommRing A`, and contributes only trivial equations.
Nonreduced algebras and nonreduced G are included, so no replacement by k-points
or density assertion occurs. A noncommutative or disconnected G is permitted.
A representation without character vectors has zero sum of eigenspaces; the
theorem still applies and does not claim that the sum is V.

Searches (2026-10-24):

- `msearch.py`, leanfinder: "Eigenspaces of distinct characters of an affine
  group scheme representation are independent and only finitely many are
  nonzero". Eight hits, including `Module.End.eigenspaces_iSupIndep`,
  `AddChar.linearIndependent` and finite-group character results; none concerns
  rational representations of affine group schemes on all algebra points.
- `msearch.py`, loogle: "Submodule.independent, DirectSum.coeLinearMap".
  Zero hits; unknown identifier `Submodule.independent`.
- `msearch.py`, grep: `character.*[Ee]igenspace|[Ee]igenspace.*character`.
  One hit, a Lie weights keyword list, not the required notion or statement.
- `msearch.py`, leansearch: "character eigenspaces affine group scheme
  independent direct sum". Eight hits, including the single-operator
  independence results and existing DirectSum independence APIs; no match.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for character eigenspaces,
  weight spaces and the item id: no declaration of the theorem. The tangent
  weight-space construction is for an internal action on a group tangent
  space and rational torus points, not an arbitrary rational linear
  representation on all algebra-valued points. Existing GL and its natural
  point equivalence were found and used. No upstream file mentions this id.
- DAG search for character eigenspaces found this node and its consumers,
  not a separate definition node carrying the notion. The helpers here
  implement the definitions that are already part of this item's statement.

Validation: the server wrapper compiled the initial module cleanly in both
sandbox and library module mode. The final module additionally makes canonical
sum-map injectivity explicit and is compiled again before delivery. No
STATEMENT-DISPUTED flag or node fault was found.

## Second reading by Q119

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
