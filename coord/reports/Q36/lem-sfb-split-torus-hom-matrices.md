## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.SplitTorusHomMatrices` states
`AlgebraicGeometry.MultiplicativeType.splitTorus_hom_matrices` and supplies two
explicit coordinate helpers for the existing product torus. All theorem proofs
are `sorry`; the helpers have actual recursive/product-projection data.

Hypotheses and clauses, with the node and Lean read together:

- A field k is `(k : Type u) [Field k]`; no algebraic closure, characteristic,
  perfectness, smoothness, or extra assumption on k is introduced.
- Nonnegative integer ranks are `(r s : ℕ)`. The objects are the already recorded
  `MultiplicativeType.splitTorus k r` and `splitTorus k s`, actual iterated products
  of `StandardGroupSchemes.multiplicative k`. Its definition at zero is the tensor
  unit, the trivial group scheme over `Spec k`.
- The displayed source is `Matrix (Fin s) (Fin r) ℤ`. Zero-based finite indexing
  simply relabels {1,...,s} and {1,...,r}; its addition is entrywise.
- `e : Matrix (Fin s) (Fin r) ℤ ≃ (splitTorus k r ⟶ splitTorus k s)` states the
  bijection with group-scheme homomorphisms. Mathlib's bundled `Grp` morphisms
  contain exactly the underlying over-scheme map with `IsMonHom`.
- The final conjunct `(e (M + N)).hom.hom = (e M).hom.hom * (e N).hom.hom`
  states preservation of the two operations, hence this bijection is the requested
  abelian-group isomorphism. `*` here is Mathlib's pointwise multiplication of
  morphisms into a group object (`CategoryTheory.Hom.group` and `Hom.monoid`),
  not composition. Expressing the isomorphism by an equivalence and its operation
  law avoids introducing another group structure on the bundled Hom type.
- Every k-scheme, affine or otherwise, is `U : Over (Spec (.of k))`.
  `p n U` identifies its points with `Fin n → Γ(U.left, ⊤)ˣ`, as multiplicative
  groups. The first conjunct fixes each value to pullback of the actual Laurent
  coordinate, so these are the canonical unit coordinates, not arbitrary choices.
- `splitTorusProjection` recursively selects the first factor or follows the
  second factor, in the existing product ordering. `splitTorusCoordinate` pulls
  back `LaurentPolynomial.T 1` using `Scheme.ΓSpecIso` and that projection.
- The middle conjunct says for EVERY matrix M, EVERY U, EVERY U-point x and
  EVERY row j that the output unit is `∏ i : Fin r, p r U x i ^ M j i`.
  Exponents are integers; negative exponents are unit inverses. `Finset.prod`
  includes the convention that an empty product is 1.

Dependency declarations used:

- `def-weil-field`: Mathlib.Algebra.Field.Defs, `Field`; its full signature is
  `class Field (K : Type u) extends CommRing K, DivisionRing K`.
- `def-sc-gm-ga`: Sheaf.AlgebraicGeometry.StandardGroupSchemes,
  `StandardGroupSchemes.multiplicative`, `multiplicativeGroup`; the former is
  `affine k (LaurentPolynomial k)`, the latter the canonical Laurent Hopf law.
  Read their signatures/docstrings and the affine/map helpers in that source.
- `def-sc-group-scheme`: Mathlib.CategoryTheory.Monoidal.Grp, `GrpObj`, `Grp`,
  and `Grp` morphisms; Mathlib.CategoryTheory.Monoidal.Mon, `IsMonHom`;
  Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, `CategoryTheory.Hom.group`.
  The recorded WeilConjectures.AlgebraicGeometry.GroupScheme.Defs documentation
  confirms this exact specialization to schemes over the spectrum of a field.
- Added already landed `def-sfb-tori-multiplicative-type` to `stmt_deps` to use
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType, `MultiplicativeType.splitTorus`,
  whose full recursive definition was read. No duplicate torus definition.

The recorded, stated proof dependencies are imported privately: affine spectra
and the affine fibre-product identification from Mathlib.AlgebraicGeometry.Pullbacks;
`Algebra.TensorProduct.productMap` and its universal property from
Mathlib.RingTheory.TensorProduct.Maps;
`AddMonoidAlgebra.isGroupLikeElem_iff_mem_range_single_one` from
Mathlib.RingTheory.Bialgebra.MonoidAlgebra;
`ΓSpec.locallyRingedSpaceAdjunction` from Mathlib.AlgebraicGeometry.GammaSpecAdjunction;
and `LaurentPolynomial` from Mathlib.Algebra.Polynomial.Laurent.
The multiplicative group and group-scheme definitions are public statement imports.
The theorem docstring gives all five proof steps of the DAG, including the coordinate
construction, group-like basis argument, inverse, arbitrary-scheme evaluation and addition.

Edge cases checked before writing: r=0 yields one empty matrix, all row formulas
are 1 and the only group morphism is the identity section; s=0 yields the unique
morphism to the trivial group and no row equations; r=s=0 combines these.
Empty U has the zero global-sections ring and a singleton unit group, so the point
identification and formula still apply. No affineness or reducedness of U is used.
Negative exponents use units. Over characteristic p, the Frobenius map corresponds
to the integer matrix (p), so the statement excludes no positive characteristic.
The test-scheme universe is the same as the field's universe, with no independent
smaller test universe. The product projection helper uses `Fin.elim0` at zero.

Searches performed:

- msearch.py LeanFinder: "Homomorphisms of split multiplicative group schemes are
  integer matrices given by Laurent monomials". Eight hits, including
  `ModularGroup.coeHom`, `Matrix.GeneralLinearGroup.upperRightHom`, and matrix GL
  maps; none classifies morphisms of group schemes.
- msearch.py Loogle: `"AlgebraicGeometry", "torus"`: zero hits.
- msearch.py LeanSearch: "Homomorphisms of split algebraic tori as group schemes
  correspond to integer matrices": group/lattice results, no matching theorem.
- msearch.py grep of Mathlib/AlgebraicGeometry:
  `splitTorus|SplitTorus|diagonalizable|split torus|split tori`: no matching
  scheme-theoretic classification.
- rg of lean/WeilConjectures with splitTorus, SplitTorus, split-torus and torus/Hom
  patterns, and the node id: no theorem for this node.
- rg of lean/Sheaf with the same patterns found the actual split torus in
  ToriMultiplicativeType and the relative classification in
  RelativeSplitTorusMatrixSheaf. The latter concerns locally constant matrices
  over arbitrary base schemes and a different explicit base-changed integral
  model; it is not this statement on the recorded product torus. Its surrounding
  definitions and full theorem were read. No copy of that model was made.
- rg of Mathlib, lean/WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json
  for splitTorusProjection, splitTorusCoordinate and splitTorus_hom_matrices found
  no existing declaration with the chosen names.

The source was opened with pdftotext from
`literature/milne-algebraic-groups_iAG2017.pdf`, Theorem 12.9(a), printed p.233,
isomorphism (76) and its finite-direct-sum/product explanation (continuing p.234).
No statement correction, new node, dependency repair or disputed statement is needed.

## Second reading by Q36

This is a separate self-review pass; the dispatcher explicitly forbids spawning
another agent. Reopened the node and the completed Lean file and checked the
field and two ranks, actual existing product object, all group-scheme morphisms,
integer matrix ordering, every-test-scheme quantifier, all rows and all columns,
coordinate normalization, addition versus pointwise multiplication, and empty-product
convention. The equality of underlying morphisms faithfully expresses the additive
law because `Grp.hom_ext` says these determine the bundled group morphisms.
The point equivalences are constrained by actual coordinate pullback, preventing
any unintended automorphism of the unit coordinates. No statement mismatch found.
The compiler caught missing parentheses in the dependent return type of the product
projection helper; these were repaired without changing its mathematical data.
