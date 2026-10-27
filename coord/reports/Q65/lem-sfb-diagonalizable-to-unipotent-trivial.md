## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableToUnipotentTrivial` states
`AlgebraicGeometry.diagonalizable_to_unipotent_trivial`, with its sole proof `sorry`.
Its docstring gives all four steps of the node's coordinate proof, including the
coefficient argument in characteristic two. No definition or auxiliary theorem is added.

Hypotheses and conclusion matched against the node:

- The field k is `{k : Type u} [Field k]`.
- The finitely generated additive abelian group M is `(M : Type u)
  [AddCommGroup M] [AddGroup.FG M]`. No torsion-free assumption is present.
- The specified D_k(M) is the already landed `(diagonalizableGroup k M).X`.
  Its definition uses `hopfSpec` of `AddMonoidAlgebra k M`, exactly the basis,
  product, coproduct, counit and antipode in the node. The dependency
  `def-sfb-diagonalizable-group` is added to stmt_deps to cite that existing
  definition instead of copying the construction in the item's original inline text.
- The positive matrix size is `(n : ℕ) (hn : 0 < n)`.
- U is `(U : Over (Spec (.of k))) [GrpObj U]`, with closed group embedding
  `j : U ⟶ GeneralLinearGroup (ULift (Fin n)) k` and
  `hj : IsClosedSubgroupScheme j`. The recorded class includes `IsMonHom j`,
  pointwise injectivity, and the closed immersion of underlying schemes.
- Being a closed subgroup of the specified unitriangular group is rendered by
  this closed embedding and `hunitriangular`: for every commutative k-algebra A
  and every A-point x of U, the corresponding matrix has every diagonal entry 1
  and every entry with column less than row 0. These are exactly the defining
  equations of the node's U_n, imposed over every algebra, including nonreduced
  algebras. This presentation has the same U and embedding: an embedding in U_n
  composes to such a closed embedding in GL_n, and conversely these equations,
  evaluated at the universal point of the affine closed subscheme U of GL_n,
  factor j through the closed subscheme U_n. The factor is a closed immersion;
  the group operations are inherited. This is not the weaker condition on
  geometric points. No independently defined unitriangular scheme is needed.
- The given homomorphism is `f : (diagonalizableGroup k M).X ⟶ U` with
  `[IsMonHom f]`, using the recorded group-scheme convention.
- The entire conclusion is the node's all-algebras conclusion: for every
  `(A : Type u) [CommRing A] [Algebra k A]` and
  `d : (Spec (.of A)).asOver (Spec (.of k)) ⟶ (diagonalizableGroup k M).X`,
  `d ≫ f = 1`. Composition is f_A, and `1` is the identity element in the
  group of U-valued points, not an identity endomorphism.
- There is no smoothness, connectedness, perfection or characteristic hypothesis
  on k, D_k(M), or U. No reducedness of test algebras is assumed.

All universes and variables are explicitly bound (`set_option autoImplicit false`).
The existing spectrum and group-scheme interfaces use a common universe u for k,
M and test algebras. `ULift.{u} (Fin n)` places the finite matrix index in that
universe, as required by the existing GL interface, without changing the matrix size.

Dependency declarations read and used:

- `Field`, in `Mathlib.Algebra.Field.Defs`, line 180.
- `CategoryTheory.GrpObj`, `CategoryTheory.IsMonHom`, and the point group structure
  `CategoryTheory.GrpObj.Hom.group`, in `Mathlib.CategoryTheory.Monoidal.Grp`,
  `Mathlib.CategoryTheory.Monoidal.Mon`, and
  `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp`, respectively.
- `AlgebraicGeometry.IsSubgroupScheme` and `IsClosedSubgroupScheme`, in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, lines 74--101;
  imported publicly. Their signatures and docstrings give precisely the node's
  group-scheme and subgroup convention. No dependency repair is necessary.
- `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`, lines 470 and 479, supplied through the
  public group-scheme imports. The test object is its standard `asOver` form.
- `Algebra.TensorProduct.instCommRing`, `includeLeft`, `includeRight`, and `ext`,
  in `Mathlib.RingTheory.TensorProduct.Basic`, and `productMap` and
  `productMap_apply_tmul`, in `Mathlib.RingTheory.TensorProduct.Maps`,
  lines 810--833. Their complete signatures were read; `Maps` is a proof import.
- `TensorProduct.lift`, `lift.tmul` and `ext'`, in
  `Mathlib.LinearAlgebra.TensorProduct.Basic`, lines 118--140, for the
  coefficient functionals in proof step 2; this is a proof import.
- `AlgebraicGeometry.diagonalizableGroup`, in
  `Sheaf.AlgebraicGeometry.DiagonalizableGroup`, imported publicly. Read the
  entire definition and docstring of `def-sfb-diagonalizable-group`.
- `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`,
  in `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`, imported
  publicly. Read its complete definition, group instance, equivalence signature
  and naturality theorem. This is the existing general-linear construction
  also used by `def-sc-general-linear-group`; no second matrix group is defined.
- `AddGroup.FG`, in `Mathlib.GroupTheory.Finiteness`, lines 398--401,
  imported publicly to express finite generation.

Sources read: Milne's supplied PDF, physical pages 243--245 (printed 231--233),
for the group algebra and diagonalizable groups, and physical pages 293--296
(printed 281--284), for formula (92), Theorem 14.5, Proposition 14.16 and
Corollary 14.18(b). The latter explicitly states this direction. The surrounding
examples explicitly include non-smooth and disconnected unipotent groups.
The module retains the node's more explicit universal-point proof, rather than
silently replacing it by the book's image argument.

Edge cases checked mathematically: M = 0 gives the trivial diagonalizable group;
n = 1 leaves no off-diagonal entries and forces the embedded U to be trivial;
U = 1 is allowed; M = Z/pZ in characteristic p includes the nonreduced mu_p;
characteristic two is covered because b_0 = 2 b_0 implies b_0 = 0 by subtraction,
not division; the zero test algebra is allowed. The unitriangular equations
are required on all algebras, so no density-of-geometric-points argument occurs.

Searches performed:

- `msearch.py`, leanfinder: "Every homomorphism from a diagonalizable group
  scheme to an upper unitriangular group scheme is trivial". Eight hits concern
  diagonal representations, scalar matrices and diagonal scheme morphisms;
  none is this statement.
- `msearch.py`, loogle: `"Unipotent", "MonoidHom"`. Zero hits.
- `msearch.py`, grep: `Diagonaliz|Unitriangular|unitriangular|diagonalizable`.
  Eighteen hits concern linear endomorphisms, spectral theory or sieve sums,
  not group schemes.
- Direct Mathlib source search for those same words found no group-scheme match.
- Direct `rg` of `lean/WeilConjectures` for `diagonaliz`, `unitriangular` and the
  item id found no statement match. The group-scheme source supplies the existing
  subgroup and GL interfaces.
- Direct `rg` of `lean/Sheaf` found the reusable diagonalizable group definition,
  nilpotent rigidity (a different theorem over rings), and the already stated
  adjoint-kernel quotient and characteristic-zero vector-group results. Read
  those matrix interfaces; both use exactly the all-algebras unitriangular
  embedding presentation adopted here. Neither states the present theorem.
- Exact proposed declaration-name searches in Mathlib, WeilConjectures, Sheaf
  and `dag/lean_names_upstream.json` found no collision.

There is no statement correction, new node, disputed statement or dependency repair.
The only node changes are its Lean record and the added landed definition dependency.
The server `scompile.py` checked both sandbox and library module names cleanly
(1.5 and 1.6 seconds respectively), with no errors or warnings.

## Second reading by Q65

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
