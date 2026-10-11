## Worker report

Module: `Sheaf.AlgebraicGeometry.MatrixSubgroupLieBracket`.
Declaration: `AlgebraicGeometry.GeneralLinearGroup.exists_tangentMatrixSubmodule_differential`.
Only its proof is `sorry`; no definition or instance is added.

The statement is the node's matrix-group assertion, using the source library's coordinate
presentation of finite-dimensional vector spaces and closed group schemes. No node correction
or additional definition is needed. The source unit `dag/units/sk-d-tangent.json` was read;
Milne's Chapter 10 was consulted at https://www.jmilne.org/math/Books/iAG2017.pdf.

Hypotheses and clauses:

- The field `k` is `[Field k] [IsAlgClosed k] [CharZero k]`, exactly the three stated hypotheses.
- Finite-dimensional `V` and `M` are presented as `n → k` and `m → k` with finite index types
  `[Fintype n]` and `[Fintype m]`. This is the existing `RationalHom.representation` convention.
  Every finite-dimensional vector space has a finite basis, including dimension zero; changing
  bases conjugates the matrices and preserves all equations here. `DecidableEq` is the data
  required by the matrix identity, available for every finite index type. No basis property or
  nonzero-dimension assumption is imposed.
- The finite-type closed subgroup scheme is `subgroupScheme I`, where `I` is an ideal of
  `Matrix.GeneralLinearGroup.CoordinateRing n k` and `[I.IsHopfIdeal k]`. This is exactly a closed
  subgroup of GL in coordinate form. The coordinate ring is finite type and Noetherian over a
  field, so no additional finite-generation binder is necessary; the source provides
  `LocallyOfFiniteType (subgroupScheme I).hom`. No radical, reduced, smooth or connected
  hypothesis is imposed.
- The displayed tangent set is the equivalence
  `X ∈ S ↔ dualUnit X ∈ Matrix.GeneralLinearGroup.zeroLocus I (DualNumber k)`.
  The imported `dualUnit` has value `1 + X.map TrivSqZeroExt.inr`, i.e. `1 + εX`, and `zeroLocus`
  means that every defining equation in `I` vanishes over the indicated algebra.
- Being a k-linear subspace is `S : Submodule k (Matrix n n k)`. Closure under the specified
  bracket is `∀ X ∈ S, ∀ Y ∈ S, X * Y - Y * X ∈ S`. By the Mathlib associative commutator
  Lie algebra and `LieSubalgebra` definition, these are precisely the Lie-subalgebra clauses.
  The statement spells these clauses out instead of activating a file-local Lie-ring instance.
- A rational representation is quantified as
  `∀ (r : RationalHom (subgroupScheme I) m) [IsMonHom r]`: a scheme morphism over k preserving
  multiplication. This uses the dependency's source definition of algebraic-group modules.
- Its derivative is `∃ d : S →ₗ[k] Matrix m m k`, so k-linearity is part of the type.
  Its characterization is: for every `X : S` and dual-number point `g` whose image in GL is
  `dualUnit X.val`, `r.points (DualNumber k) g = dualUnit (d X)`.
  The imported `zeroLocusMulEquiv` shows such a point exists for every X by the carrier
  equivalence above, and the closed immersion is injective on points. Thus this is the node's
  equation for r(1+εX), without adding a hypothesis or making the characterization vacuous.
  Injectivity of `dualUnit` (read off its ε coefficient) makes d unique; consequently the
  existential characterization states the claim about the derivative specified in the node.
- Bracket preservation is
  `∀ X Y Z : S, Z.val = X.val * Y.val - Y.val * X.val → d Z = d X * d Y - d Y * d X`.
  The closure clause supplies Z for every X,Y, uniquely as a subtype element. Hence this
  says precisely `dr([X,Y]) = dr(X)dr(Y) - dr(Y)dr(X)`, with no weaker implication and no
  choice of an additional bracket. A linear map with this property is exactly the Lie
  representation of `def-wf-lie-algebra`.

Dependency declarations read and used:

- `def-wf-algebraic-representations`: source module
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.ClosedSubgroup.Lie`,
  `AlgebraicGeometry.GeneralLinearGroup.standardRepresentation`, and source module
  `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Representation`,
  `AlgebraicGeometry.GeneralLinearGroup.RationalHom.representation`. Their signatures and
  docstrings use the underlying `RationalHom` and `[IsMonHom r]` adopted here. The theorem
  concerns the scheme homomorphism on dual-number points rather than just the k-point action.
- `def-wf-lie-algebra` is a Mathlib leaf: read `LieRing`, `LieAlgebra`, `LieModule` in
  `Mathlib.Algebra.Lie.Basic`, `LieSubalgebra` in `Mathlib.Algebra.Lie.Subalgebra`, and
  `LieRing.ofAssociativeRing`, `LieAlgebra.ofAssociativeAlgebra`, `LieModule.toEnd` in
  `Mathlib.Algebra.Lie.OfAssociative`. They justify the explicit subspace/commutator formulation.
- Supporting existing source definitions read: `dualUnit`, `RationalHom`, `RationalHom.points`
  and `RationalHom.differential` in `GeneralLinear.Lie`; `subgroupScheme`, `subgroupSchemeι`,
  `zeroLocusMulEquiv` in `GeneralLinear.ClosedSubgroup`; `zeroLocus` in
  `WeilConjectures.RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`.
  All are available through the single import of the dependency's recorded module.

Edge cases checked before writing: n empty (V=0 and GL trivial), m empty (zero representation),
I=0 (G=GL), the identity subgroup, X=0 and X=Y (zero commutator), and nonradical Hopf ideals.
None require a Nonempty or reducedness hypothesis. All types live in a common explicitly bound
universe, matching the source scheme-point API; simultaneous lifting covers differently sized
carriers. All variables and the universe are explicit.

Searches for an existing full statement:

- msearch leanfinder: `Lie algebra of closed matrix subgroup scheme dual numbers commutator
  differential rational representation`: eight hits, including special-linear and Serre/Geck
  constructions; no exact scheme-tangent statement.
- msearch loogle: `LieSubalgebra, LieHom.map_lie`: zero hits.
- msearch grep: `dualUnit|LieSubalgebra|GroupScheme`, subdirectory `Algebra/Lie`: 25 hits on
  generic LieSubalgebra API, no algebraic-group-scheme theorem.
- rg on Mathlib Lie Basic/Subalgebra/OfAssociative/Matrix: generic structures and the matrix
  commutator exist, but no membership theorem for the specified closed subgroup.
- rg over source `WeilConjectures` and project `lean/Sheaf` for
  `lem-wf-lie-algebra-derivation-bracket|dualUnit.*(lie|commut)|lie.*dualUnit|differential.*(lie|dual)`:
  general differentials and tangent equivalences, no declaration combining the full carrier
  identification, closure and differential characterization in this node. Read
  `GeneralLinear.Lie` and `GeneralLinear.ClosedSubgroup.Lie` in full. The existing LieHom
  differential supplies linearity/bracket preservation on `GrpObj.Lie`, but alone does not state
  this theorem about the displayed tangent-matrix subset. It is reused, not redefined here.
- rg over source, project and `dag/lean_names_upstream.json` for
  `exists_tangentMatrixSubmodule_differential|tangentMatrixSubmodule|lem-wf-lie-algebra-derivation-bracket`:
  no hits and no declaration-name collision.

Validation: scompile.py compiled the module on the server in 2.1 seconds with exit code 0,
no errors or warnings. The docstring records each of the node's five proof steps and its
non-elementary dependencies. No statement dispute or node fault was found.

## Second reading by R1

Independent reading of the node, its unit `sk-d-tangent`, the complete delivered module,
its two statement-dependency nodes, and the source declarations named below. Verdict:
the signature renders every object, hypothesis and conclusion of the node; no Lean or
node repair was necessary. This reading adds the missing independent-review record.

Source check: this node cites Milne, not Stacks, so there is no Stacks tag or standing
Stacks hypothesis to recover. Read Milne's *Algebraic Groups* (2017), Chapter 10,
sections 10.6–10.7, 10.11, 10.18–10.24 and the representation paragraph before 10.31,
from https://www.jmilne.org/math/Books/iAG2017.pdf. These give the infinitesimal-point
interpretation, its linear operations, the matrix commutator and functorial bracket
preservation. The chapter works with affine algebraic groups over a field; this node
explicitly specializes to algebraically closed characteristic zero. It does not assume
smoothness or connectedness. The finite-type closed subgroup scheme description also
agrees with the unit's allowance of nonradical defining ideals.

Object/hypothesis/conclusion checklist, independently transcribed from the node:

1. An algebraically closed field k of characteristic zero: `{k : Type u} [Field k]
   [IsAlgClosed k] [CharZero k]`. Exact; no stronger field hypothesis.
2. Two finite-dimensional k-vector spaces V and M: the coordinate spaces `n → k` and
   `m → k`, with `[Fintype n] [Fintype m]`. Every finite-dimensional vector space has a
   finite basis; its endomorphisms identify with these matrices, with composition
   identifying with matrix multiplication. A basis change conjugates all the displayed
   equations. `[DecidableEq n] [DecidableEq m]` supplies equality decisions for the
   matrix identity and is available classically for every index type. These are coordinate
   data, with no restriction on dimension or representation. Exact in the dependency's
   existing coordinate convention, rather than a special kind of vector space.
3. A finite-type closed subgroup G of GL(V): the arbitrary ideal
   `I : Ideal (Matrix.GeneralLinearGroup.CoordinateRing n k)` with `[I.IsHopfIdeal k]`,
   and `subgroupScheme I`. Read `subgroupScheme`, its group-object instance,
   `LocallyOfFiniteType`, `subgroupSchemeι`, its closed-immersion and monomorphism
   instances in `GeneralLinear.ClosedSubgroup`. This is the quotient coordinate algebra
   of the closed group subscheme; every closed subgroup has such a Hopf ideal. Finite
   type follows from the finite matrix coordinate ring. Exact; no radical or finiteness
   assumption on a different object is substituted.
4. The displayed tangent subset: `∀ X : Matrix n n k, X ∈ S ↔ dualUnit X ∈
   Matrix.GeneralLinearGroup.zeroLocus I (DualNumber k)`. Read `dualUnit` in
   `GeneralLinear.Lie`: its matrix is `1 + X.map TrivSqZeroExt.inr` and its inverse
   is `1 - X.map TrivSqZeroExt.inr`. Read `zeroLocus` in
   `RingTheory.HopfAlgebra.GeneralLinearGroup.HopfIdeal`: its carrier requires the
   evaluation of every element of I to vanish. Thus this is precisely membership of
   `1 + εX` in G over k[ε]/ε², including scheme-theoretic equations. Exact.
5. This subset is a k-linear subspace and is closed under `[X,Y] = XY - YX`:
   `∃ S : Submodule k (Matrix n n k)` together with
   `∀ X ∈ S, ∀ Y ∈ S, X * Y - Y * X ∈ S`. Exact. Read Mathlib
   `LieSubalgebra` (extends `Submodule`, adding bracket closure), `LieRing`,
   `LieAlgebra`, `LieModule` and `LieAlgebra.ofAssociativeAlgebra`. The commutator
   on matrices is precisely their associative Lie bracket. Stating these defining
   clauses introduces no competing definition and implies the asserted Lie subalgebra.
6. Every rational representation r:G→GL(M):
   `∀ (r : RationalHom (subgroupScheme I) m) [IsMonHom r]`. Read the abbreviation
   `RationalHom`, `RationalHom.points` and `RationalHom.representation` and the
   dependency's `standardRepresentation` declaration. The first is a morphism in
   `Over (Spec k)`; `IsMonHom` requires preservation of the group operations.
   `points` is the resulting group homomorphism on algebra-valued points, not merely
   an arbitrary action on k-points. Exact, using the recorded dependency's notions.
7. Its differential is characterized by r(1+εX)=1+εdr(X), and is k-linear:
   `∃ d : S →ₗ[k] Matrix m m k` with the quantified equality on dual-number points.
   The premise `homMulEquiv n k (DualNumber k) (g ≫ subgroupSchemeι I) =
   dualUnit X.val` identifies the input point. Read `range_homMulEquiv_comp`,
   `injective_homMulEquiv_comp`, `zeroLocusMulEquiv` and
   `homMulEquiv_zeroLocusMulEquiv_comp`. For each X:S there is exactly one such g,
   supplied by `zeroLocusMulEquiv I (DualNumber k)` applied to its membership proof.
   Consequently the implication is never vacuous. Comparing ε coefficients makes
   `dualUnit` injective, so this characterization determines d uniquely; existence
   as a linear map is equivalent to linearity of the map specified by the node.
   Exact. The existing `RationalHom.differential` is a Lie homomorphism on `GrpObj.Lie`;
   this theorem concerns the specified matrix carrier rather than redefining it.
8. Preservation of brackets and therefore the Lie representation on M:
   `∀ X Y Z : S, Z.val = X.val * Y.val - Y.val * X.val →
   d Z = d X * d Y - d Y * d X`. The preceding closure clause supplies Z for
   every pair X,Y; subtype extensionality makes it unique. Hence this is exactly
   the node's bracket formula, with no additional condition on X,Y. Together with
   linearity it is the usual Lie representation into End(M). Exact. S precedes the
   universal representation binder, as the node's tangent subspace does.

Edge cases: empty n and empty m are permitted (V=0 and M=0); matrices and their
commutators are then zero, with the unique invertible empty matrix. X=0 and X=Y
are included. I=0 gives GL itself, and the identity subgroup is included. Nonradical
Hopf ideals are permitted. An empty group scheme is not an omitted case: the group
identity gives a k-point. Positive characteristic is excluded by the node itself,
not by an accidental Lean hypothesis. The explicitly bound universe u is arbitrary;
finite-dimensional spaces of any carrier universe can be represented by finite
coordinate types at the field universe, or all carriers can be lifted to a common
universe. No test-algebra quantifier in a smaller universe is used. No unbound
variable or universe remains in the signature.

Independent searches (different queries from the worker):

- msearch leanfinder `closed algebraic matrix group infinitesimal tangent subspace
  differential bracket preservation`: eight hits, principally manifold GroupLieAlgebra
  and the special-linear matrix bracket; none states the closed group scheme assertion.
- msearch loogle `LieHom, Matrix`: two hits (`LieModule.toEnd_matrix` and a Geck
  trace identity); neither supplies the tangent carrier or this representation theorem.
- msearch grep `infPointsEquivTangentGroup|zeroLocus|dualUnit`: generic geometric
  zero-locus hits, no full theorem. Direct rg on Mathlib Lie files confirms the generic
  associative bracket/subalgebra structures, rather than this group scheme theorem.
- Direct rg on source `WeilConjectures` and project `lean/Sheaf` using `dualUnit`,
  `infPointsEquivTangentGroup`, `lieAlgebraEquivMatrix`, and matrix tangent/bracket
  phrases. Read the related source signatures: the GL tangent equivalence, the
  `GrpObj` differential, `mem_range_dualCotangentToMatrixₗ` (carrier identification),
  and `lie_mem_range_lieAlgebraMap` (a different inclusion assertion). None is the
  full statement combining this specified carrier, closure and dual-point differential.
  There is no existing project theorem to record instead. The upstream-name index
  contains the GL equivalence but no collision with this declaration's full name.

H4–H9 and H12–H13: no new definition node, dependency module, private notion, local
notation or local instance is delivered. Both dependency nodes were checked against
the source declarations/Mathlib signatures just listed and are usable. No statement
correction record exists or is needed. The only theorem proof is `sorry`, and there
is no new definition whose data could be hollow. The docstring gives the source,
blueprint id and all five proof steps, including mixed-commutator and representation
naturality dependencies. Header, namespace and 100-character Lean line widths conform.
The node's `lean.statement` matches the unchanged file signature verbatim.

Validation: independently ran scompile.py for the delivered module: compiled in 2.8 s,
exit code 0, no errors or warnings. Initial dry run found only the absent second-reading
section; this appended section repairs that delivery-record mismatch.
