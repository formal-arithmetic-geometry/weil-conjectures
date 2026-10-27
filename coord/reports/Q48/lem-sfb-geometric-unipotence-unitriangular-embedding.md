## Worker report

The module `Sheaf.AlgebraicGeometry.GeometricUnipotenceUnitriangularEmbedding` states
`AlgebraicGeometry.geometric_unipotence_unitriangular_embedding`, with one whole-proof
`sorry` and no definitions. It states the item without changing its informal statement
or dependencies. In particular, the conclusion spells out the polynomial chart and
matrix entries of the unitriangular group rather than leaving its meaning implicit.
The existential group U is characterized in the conclusion itself; there is no chosen
unspecified object and no new predicate or duplicate definition.

Hypotheses and clauses, in the order of the node:

- The base field is `{k : Type u} [Field k]`.
- The k-group scheme is `(G : Over (Spec (.of k))) [GrpObj G]`. Its multiplication,
  identity and inverse are the existing categorical group object data.
- Smoothness, affineness and finite type are `[Smooth G.hom]`, `[IsAffine G.left]`,
  and `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, respectively.
- The positive representation dimension is `(m : ℕ) (hm : 0 < m)`.
- The representation is `rho : G ⟶ GeneralLinearGroup (ULift.{u} (Fin m)) k`,
  with `[IsMonHom rho]` expressing the homomorphism condition. ULift preserves exactly
  the m indices while placing them in the common universe required by upstream GL.
- `hinj` quantifies over every commutative k-algebra R and asserts injectivity of
  `fun x ↦ x ≫ rho`. Its domain is precisely morphisms Spec R to G over Spec k.
- `hunip` quantifies over G-points valued in `AlgebraicClosure k`; the existing
  `GeneralLinearGroup.homMulEquiv` gives their matrices. The existential N is a positive
  natural number and the equation is `(matrix - 1)^N = 0`. N can depend on the point.
- The conclusion has `∃ n : ℕ, 0 < n` and a group scheme U over the SAME Spec k.
- It supplies `f : G ⟶ U.X` and `j : U.X ⟶ GeneralLinearGroup ... k`, with
  `IsMonHom f` and `IsMonHom j`. The requested i is their composite f ≫ j; both its
  group homomorphism property and its factorization follow directly from these data.
- `IsClosedImmersion (f ≫ j).left` explicitly states the requested closed immersion i;
  `IsClosedImmersion f.left` states that the factor G to U is a closed immersion.
  `IsClosedImmersion j.left` states that U is a closed subgroup of GL_n.
- The chart `e` identifies U, as a k-scheme, with
  `Spec (MvPolynomial {p : Fin n × Fin n // p.1 < p.2} k)` over Spec k. This is exactly
  the polynomial algebra in the strict upper entries; 0-based Fin indices are the
  relabeling of the source's 1-based indices.
- For every R and every algebra map phi from that polynomial algebra to R, the final
  equation identifies the matrix of its corresponding U-point: it is phi(X_ab) for
  a<b, 1 for a=b, and 0 otherwise. Every U-point arises this way by the affine Spec
  correspondence and the chart e. Conversely arbitrary upper entries define such a
  phi by the polynomial universal property. Thus these are exactly U_n(R), not merely
  some subgroup with upper unitriangular points. Since j is a homomorphism, the law
  is exactly matrix multiplication under this identification.
- The original field occurs in all the conclusion's schemes and morphisms; no field
  extension is used there. There is no perfectness, connectedness or characteristic
  assumption.

Dependencies read and used:

- `Mathlib.Algebra.Field.Defs`, `Field` (def-weil-field).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`
  (def-sbc-smooth-morphisms).
- `Mathlib.CategoryTheory.Monoidal.Grp`, `CategoryTheory.GrpObj` and `CategoryTheory.Grp`,
  and the existing `CategoryTheory.IsMonHom` interface (def-sc-group-scheme). The
  specialization to group schemes was checked in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`,
  and `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`
  (def-weil-finite-type-morphism).
- The recorded `Sheaf.AlgebraicGeometry.LinearGroupSchemes` is publicly imported. Its
  general-linear construction is explicitly the upstream
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`,
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`;
  their full definitions and docstrings were read. We use those existing constructions,
  as the recorded dependency requires, rather than introducing another GL.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion` (def-weil-closed-immersion).
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `AlgebraicClosure` and its canonical
  field/algebra/closure instances (def-weil-algebraic-closure).

The three nondefinition proof prerequisites (faithful-closed-immersion,
fixed-vector, and invariant-descent) have no Lean records in the read repository.
They are not needed to type this statement and were therefore not imported or restated.
The full five-step node proof, naming those prerequisites, is in the theorem docstring.

Source read: the local Milne PDF, printed pp.281-283 (PDF pp.293-295), including
Theorem 14.5, its explicit coordinate algebra for U_n, Corollary 14.9 and
Corollary 14.12. The latter explicitly needs smoothness but no perfectness assumption.
The proof docstring retains the node's faithful-immersion, quotient-flag, invariant-descent,
base-field basis and coordinate-quotient argument.

Edge cases checked before writing:

- m=1 is allowed: unipotence forces the one-dimensional matrix to be 1 and faithfulness
  forces G trivial. n=1 has no strict upper coordinates; the polynomial algebra is k.
- The trivial group is allowed; the group scheme is never forced connected or positive
  dimensional. Finite etale p-groups in characteristic p are not excluded.
- Imperfect fields and wound unipotent groups are retained. The conclusion concerns a
  closed subgroup of U_n, not an isomorphism with a split unipotent group.
- Nonreduced test algebras and the zero algebra are included by `[CommRing R]`; no
  reducedness or nontriviality assumption appears in `hinj` or the coordinate chart.
- The exponent is point-dependent and positive; no uniform exponent is assumed.
- The nonsmooth counterexample mu_p is excluded precisely by the stated smoothness.
- The algebra of coordinates and the algebraic closure live in Type u, so all algebras
  needed for the universal-point and geometric-point arguments are among the test objects.
  ULift is just the finite-index universe transport, not a dimension restriction.

Searches (2026-10-24):

- msearch leanfinder: "A smooth affine group scheme with a faithful representation whose
  geometric points are unipotent embeds in the upper unitriangular group scheme over
  the base field". Eight hits on unrelated affine limits and topological special-linear
  embeddings; no matching theorem or unitriangular scheme.
- msearch loogle: "GeneralLinearGroup, IsClosedImmersion". No hits; GeneralLinearGroup
  was not recognized as an unqualified identifier by the service.
- msearch grep: "unitriangular|upperTriangular|IsUnipotent". Twenty-five displayed hits
  on matrix triangularity, cusp stabilizers and determinants; no unitriangular scheme.
- msearch leansearch: "Upper unitriangular group scheme represented by the polynomial
  algebra in strictly upper diagonal matrix entries". Eight hits on triangular
  characteristic polynomials, cusp groups, smooth polynomial rings and unitary groups;
  no scheme construction or embedding theorem.
- rg in lean/WeilConjectures for unitriangular, IsUnipotent, and geometric unipotence:
  only an unrelated matrix inverse docstring; grep for the exact item id had no hits.
- rg in lean/Sheaf: geometric-unipotence uses are proof plans; existing
  SolvableGroupStructure.IsUnipotent describes geometric matrix unipotence, not this
  embedding. AdjointKernelCentralQuotientUnipotent uses pointwise upper equations in a
  different theorem. Neither states this result or constructs the general U_n.
- rg in dag/lean_names_upstream.json for the item id: no match.

Validation: scompile.py checked both the sandbox and intended library module successfully
(16.9 s and 5.5 s), without errors or unexpected warnings. No statement dispute or
statement correction was needed.

## Second reading by Q48

This is the author's separate clause check; the delivery receives the maintainer's
independent review. I reopened the node and Lean signature and checked the conditions
against Milne pp.281-283. The rank is positive on both sides, injectivity is on ALL
algebra points, the nilpotence condition is only on algebraic-closure points and has a
point-dependent positive exponent, and both maps in the factorization are over k.
The chart specifies every entry, not just the geometric points; its polynomial
coordinates ensure that U is the whole unitriangular group. IsMonHom j transports
matrix multiplication to the group law on U, and f is closed separately from the
composite. The three cases of the entry formula are exhaustive and agree with the
source, including n=1. No mismatches were found and no node field other than lean changed.
