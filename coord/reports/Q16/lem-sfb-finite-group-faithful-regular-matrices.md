## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.FiniteGroupFaithfulRegularMatrices`.
The theorem is `AlgebraicGeometry.finite_group_faithful_regular_matrices`, with its proof
postponed by `sorry`. Its transparent conclusion predicate
`AlgebraicGeometry.FiniteGroupRegularMatrices` has a complete, concrete Prop-valued body.
It packages this node's own clauses, and introduces no independent mathematical notion,
new group scheme, coordinate algebra, or chosen action. The predicate is listed in
`lean.declarations`, as permitted for helpers belonging to the same notion.

Read the node and all six statement dependencies, their records and the applicable source
signatures/docstrings. Read Milne iAG2017, Remark 4.1 and equations (24)--(25), printed p.84;
the right-translation convention and Theorem 4.9 proof, printed p.87; and Proposition 11.32,
printed p.221. The matrix index convention agrees with those passages.

Hypothesis and clause correspondence:

- A field k: `k : CommRingCat.{u}` and `hk : IsField k`. This expresses that the GIVEN
  commutative ring is a field, without replacing its ring structure by a second instance.
  `IsField.toField` supplies a Field structure when a future proof needs it. Every field
  can be bundled as `CommRingCat.of k`.
- A finite k-group scheme: `G : Scheme.{u}`, `[G.Over (Spec k)]`,
  `[GrpObj (G.asOver (Spec k))]`, and `[IsFinite (G ↘ Spec k)]`. This is the unbundled
  version of the recorded `GrpObj` on `Over (Spec k)`, with the same structure morphism.
  No `IsCommMonObj`, reducedness, etaleness, characteristic or algebraic-closure assumption.
- A = Gamma(G,O): every occurrence is the ACTUAL `Γ(G, ⊤)`. The canonical Algebra and
  HopfAlgebra instances are those of Mathlib.AlgebraicGeometry.Group.Affine. They transport
  the given group law along `G.isoSpec`; no arbitrary Hopf algebra is supplied.
- d = dim_k A and choosing a basis: the basis `b` has index
  `LinearGroupSchemes.Index.{u} (Module.finrank k Γ(G, ⊤))`. This is `ULift (Fin d)`
  from the recorded GL dependency, with exactly d elements; the lift fits the upstream
  common universe of the finite matrix indices, field, schemes and test algebras.
- The group-scheme homomorphism rho to GL(A): `ρ` is a morphism from `G.asOver (Spec k)`
  to the existing `GeneralLinearGroup` on this basis, and `IsMonHom ρ` is required.
  This is the basis presentation of GL(A), not an abstract group representation on k-points.
  Its intrinsic action is simultaneously stated in the following tensor clause.
- Closed immersion: `IsClosedImmersion ρ.left`, using the recorded Mathlib class.
  The theorem passes `isAffine_of_isAffineHom (G ↘ Spec k)` to the conclusion predicate;
  affineness is derived from finiteness, never assumed as an additional hypothesis.
- The coordinate homomorphism k[T_ij,det^-1] -> A: `φ` has source the existing
  `Matrix.GeneralLinearGroup.CoordinateRing`, which is exactly the localization away from
  the generic determinant. `Function.Surjective φ` is explicit.
  The equation `ρ.left = G.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)`
  identifies this with rho's induced coordinate map, rather than an unrelated surjection.
- T_ij -> u_ij: `φ (Matrix.GeneralLinearGroup.coord _ k i j) = U i j`.
  The equation `Coalgebra.comul (b j) = sum_i b i tensor U i j` fixes these as the
  regular coproduct coefficients. It rules out an unrelated faithful representation.
- Evaluation at identity: `Coalgebra.counit (U i j) = if i = j then 1 else 0`.
  This is the canonical group-scheme counit, not an arbitrary algebra map.
- GL(A)(R) = Aut_R(A tensor R): for every `R : Type u`, `[CommRing R]`, `[Algebra k R]`,
  the conclusion supplies a monoid homomorphism `t` from G(R) into R-linear automorphisms
  of `Γ(G, ⊤) ⊗[k] R`. Its explicit `LinearEquiv` type uses the existing
  `Algebra.TensorProduct.rightAlgebra` in both module-instance positions, so R acts on
  the RIGHT tensor factor, exactly as the node requires. The basis-vector formula
  `t x (b j tensor r) = sum_i b i tensor (x(u_ij)*r)` fixes this intrinsic operator
  uniquely on a spanning family. These are precisely the same matrices as rho's points.
  Thus changing basis conjugates the matrix presentation of the same operators.
- All-algebra specialization: the first clause under R asserts that the (i,j) entry of
  `GeneralLinearGroup.homMulEquiv _ k R (x ≫ ρ)` is the evaluation of U_ij along the
  actual algebra-valued point. `Spec.preimage (x.left ≫ G.isoSpec.hom)` is its coordinate
  ring map A -> R. `homMulEquiv` is the recorded natural matrix identification.
- Products for every R: the final clause is exactly rho_R(x*y)=rho_R(x)*rho_R(y).
  The monoid homomorphism `t` also packages preservation of identity and multiplication
  for the intrinsic operators. Natural dependence on R is fixed by the scheme morphism
  rho and the coordinate evaluation/basis-vector formulas, not chosen independently.

The explicit instances inside the predicate only expose affineness and the EXISTING GL
GrpObj structure. There are no file-local instances, private definitions or local notation.
All variables/universes are explicit, and `set_option autoImplicit false` verifies that.
The `letI`s occur inside the definition's body, not inside the theorem signature.

Dependency declarations used:

- `Field` / `IsField`, Mathlib.Algebra.Field.Defs and Mathlib.Algebra.Field.IsField;
  `IsField` expresses the same field property for the bundled existing ring.
- `CategoryTheory.GrpObj` and `IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp and Mon;
  group-scheme conventions imported through
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `TensorProduct`, `TensorProduct.mk` and its universal property,
  Mathlib.LinearAlgebra.TensorProduct.Defs/Basic; right-factor module structure
  `Algebra.TensorProduct.rightAlgebra`, Mathlib.RingTheory.TensorProduct.Basic.
- `Module.finrank`, Mathlib.LinearAlgebra.Dimension.Finrank; `Module.Basis`.
- `LinearGroupSchemes.Index`, Sheaf.AlgebraicGeometry.LinearGroupSchemes, the recorded
  def-sc-general-linear-group module. Its public upstream import provides the actual GL:
  `AlgebraicGeometry.GeneralLinearGroup`, `GeneralLinearGroup.homMulEquiv`, and
  `GeneralLinearGroup.instGrpObjOverSchemeSpecOf`, in
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.
  `Matrix.GeneralLinearGroup.CoordinateRing` and `coord` are in
  WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.
- `AlgebraicGeometry.IsClosedImmersion`, Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- The proof dependency lem-sfb-affine-group-coordinate-hopf is the existing canonical
  global-section Hopf instance in Mathlib.AlgebraicGeometry.Group.Affine: it is used
  directly by `Coalgebra.comul` and `Coalgebra.counit`.
- Proof-plan imports cover Matrix.cauchy_binet, localization universal properties and
  affine fibre-product/closed-immersion criteria; their Mathlib modules and recorded
  upstream CauchyBinet module are imported, directly or through the statement imports.

Edge cases checked mathematically before writing: the trivial group has A=k and d=1,
U=(1), and surjective evaluation from k[T,T^-1]. A finite group scheme cannot have A=0
or d=0, since its counit is a unital map to a field; no extra positivity assumption is
introduced. Nonabelian constant finite groups retain the right-translation order
(t_x t_y)(a)(z)=a((zx)y). Infinitesimal groups such as alpha_p and mu_p are retained:
G(R) is tested on all algebras, not just reduced rings or k-points. The zero test algebra
is permitted; its tensor module is zero and its matrix group trivial. Dimension and
matrix indices have matching universes; no unrelated lower test universe is quantified.

Searches actually run:

1. msearch.py leanfinder, query: "The regular representation of a finite group scheme is
   a closed immersion into the general linear group of its coordinate algebra".
   Eight hits, including TannakaDuality.FiniteGroup.rightFDRep/rightRegular/leftRegular
   and PreGaloisCategory.autEmbedding_isClosedEmbedding; none states this scheme result.
   Read Mathlib.RepresentationTheory.Tannaka lines 76--106: these are representations of
   abstract groups on function spaces, and do not handle nonreduced group schemes.
2. msearch.py loogle, query: "HopfAlgebra, Matrix.GeneralLinearGroup". Zero hits.
3. msearch.py grep, query: "regularRepresentation|regular_representation|closedImmersion.*[Rr]epresentation",
   subdirectory AlgebraicGeometry. Zero hits.
4. msearch.py leansearch, query: "A finite group scheme admits a faithful regular
   representation into the general linear group scheme". Eight hits, all abstract-group
   representation declarations (TannakaDuality and Rep/FDRep); no exact match.
5. rg on project WeilConjectures and Sheaf for faithfulRegular, regularRepresentation,
   regular_representation and the node id: only the downstream OrderAnnihilator proof
   docstring cites this item. Read the existing GeneralLinear and group-scheme definitions;
   their rational representation APIs do not state the regular-embedding theorem.
6. rg for the delivered declaration names in Mathlib, WeilConjectures, Sheaf and
   dag/lean_names_upstream.json found no existing declarations with these names.

No node statement correction, disputed statement, missing dependency or new node.
The former CompactObject example module is withdrawn on the current base, so its header
is not reusable; this file follows the current module/public-section convention.

Validation: the prescribed scompile.py compiles the final module under both its sandbox
and library module paths with no errors and no non-sorry warnings. All definitions have
real bodies; the single postponed theorem carries the full source-based six-step proof
plan via its docstring and the immediately preceding predicate's docstring.

## Second reading by Q16

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
