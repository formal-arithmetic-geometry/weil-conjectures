## Worker report

Module: `Sheaf.AlgebraicGeometry.UnipotentToMultiplicativeTrivial`.
All four theorems have `sorry` as their entire proof. The three predicate definitions
contain real formulas and no postponed data. The module states every assertion of the node:

- The base is `{k : Type u} [Field k]`.
- Group schemes and their homomorphisms are `Grp (Over (Spec (.of k)))` and `V ⟶ D`.
- Affineness is `[IsAffine V.X.left]` and `[IsAffine D.X.left]`.
- Finite type is `[LocallyOfFiniteType ...] [QuasiCompact ...]` for each group.
- `HasUnitriangularEmbedding` requires a positive integer n, a
  `IsClosedSubgroupScheme ρ` into the existing `GeneralLinearGroup (ULift (Fin n)) k`,
  diagonal entries equal to 1, and every entry with j < i equal to 0, on EVERY
  commutative k-algebra A. These equations are exactly factorization through U_n;
  because U_n is closed in GL_n, a closed immersion into GL_n factoring through it
  is also a closed immersion into U_n. There is no need to choose or reconstruct
  the representing group U_n. `ULift` gives the same finite matrix index in Type u.
- `IsGeometricallyUnipotent` applies that embedding condition to scalar extension
  to `AlgebraicClosure k` using the existing `MultiplicativeType.baseChange`.
  This is the definition explicitly given in this node; the smooth-only predicate
  in `SolvableGroupStructure` would incorrectly exclude alpha_p.
- Multiplicative type is exactly the existing `MultiplicativeType.IsMultiplicativeType`:
  its definition is a closed subgroup inclusion over `AlgebraicClosure k` into
  `MultiplicativeType.splitTorus` of any finite rank, including rank zero.
- `isGeometricallyUnipotent_baseChange_iff` and
  `isMultiplicativeType_baseChange_iff` express both preservation and reflection
  along any field extension `[Field K] [Algebra k K]`, not just algebraic extensions.
- `isGeometricallyUnipotent_iff_geometric_points` has `[Smooth G.X.hom]` and no
  connectedness assumption. Its right side is a positive-dimensional faithful
  representation (`IsSubgroupScheme`, hence injective on every algebra) with
  `(ρ(x)-1)^N = 0` for some positive N at every algebraic-closure-valued point.
- `hom_to_multiplicativeType_trivial` assumes the geometric embedding condition on V
  and multiplicative type on D. Its conclusion `v ≫ f.hom.hom = 1` says f_A(v)=1,
  for arbitrary `(A : Type u) [CommRing A] [Algebra k A]` and arbitrary A-point v.
  Scoped `MonObj` supplies precisely the group of A-valued points. Neither group
  has a smoothness, reducedness, perfectness, commutativity, or connectedness binder.

The node's geometric embedding terminology is rendered by named helper definitions
in its owning module, with this node's blueprint/source docstrings, as authorized
by the missing-helper rule. It is not an independent new notion absent from the DAG:
this very node defines it. No new node or dependency-module replacement is supplied.
Added the already landed `def-sfb-tori-multiplicative-type` to `stmt_deps` to cite
its exact reused predicates and scalar-extension interface. No statement correction.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field` (def-weil-field).
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, group homomorphisms and
  the group of generalized points (def-sc-group-scheme).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme` and
  `IsClosedSubgroupScheme` (def-sc-group-scheme-subgroup).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, with
  `QuasiCompact` from Morphisms.QuasiCompact (def-weil-finite-type-morphism).
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (def-sbc-smooth-morphisms).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace` was read; no connectedness
  assumption occurs, in agreement with the node's explicit last sentence.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `multiplicative` and
  `multiplicativeGroup` (def-sc-gm-ga), used through `splitTorus`.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`, and
  Basic's `IsAlgClosure` (def-weil-algebraic-closure).
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `baseChange`, `splitTorus`,
  `IsMultiplicativeType` (def-sfb-tori-multiplicative-type).
- `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear`:
  `GeneralLinearGroup`, its group instance and `homMulEquiv`.

Proof-dependency modules are imported without `public`: the already recorded
`Sheaf.AlgebraicGeometry.AlgClosedGroupEmbeddingExistenceDescent`, and
`Mathlib.AlgebraicGeometry.Pullbacks` for `pullbackSpecIso`. `IsAlgClosed.lift`,
`IsClosedImmersion`, `Spec`, and the standard multiplicative group are available
through the statement imports. The remaining three representation/fixed-vector
proof nodes currently have no Lean records or upstream declarations; there is no
module to import for them. The proof docstrings retain all four DAG proof steps
and name their exact supporting nodes.

Sources read locally: Milne iAG2017, Theorem 14.5, Corollaries 14.6, 14.9,
14.10--14.12, Proposition 14.16, Corollary 14.18 and Example 14.19 (pp.281--284),
and Definition 12.17 and Theorem 12.23 (pp.236,240). In particular Example 14.19
explicitly allows nonsmooth alpha_p and disconnected constant Z/pZ in characteristic p.

Edge cases checked before writing: the trivial group embeds in U_1, so positive
matrix size loses no trivial case; rank-zero split torus is allowed; zero A is
allowed and has singleton point groups; nonreduced A are tested, not discarded;
alpha_p and disconnected constant p-groups are not excluded; mu_p is NOT declared
unipotent from its trivial geometric points (the point criterion requires Smooth).
There is no characteristic or perfectness restriction. The theorem is universe
polymorphic, and test rings share the field/scheme universe, as in the existing
subgroup and GeneralLinearGroup interfaces; the type of tests cannot fall below
that of k. Arbitrary field extensions in that universe are allowed.

Searches actually run:

- msearch leanfinder: "Every homomorphism from a unipotent affine group scheme to a
  group scheme of multiplicative type is trivial": eight unrelated hits, including
  `CategoryTheory.Grp.uniqueHomFromTrivial`, `CommGrp.uniqueHomFromTrivial` and
  affine-space maps. None is this statement.
- msearch loogle: `"IsUnipotent"`: 0 hits.
- msearch grep: `unipotent.*(multiplicative|diagonalizable|torus)|IsUnipotent`: 0 hits.
- rg of `lean/WeilConjectures`, `lean/Sheaf`, Mathlib and
  `dag/lean_names_upstream.json` for unipotence, unitriangularity and proposed names:
  the existing smooth `SolvableGroupStructure.IsUnipotent` is unsuitable; no
  nonsmooth geometric predicate or matching vanishing theorem was found.
  Existing inline unitriangular equations in CharZeroCommutativeUnipotentVectorGroup
  agree with the rendering here. Existing ToriMultiplicativeType supplies the
  multiplicative-type predicate, split torus and canonical scalar extension.
- rg of `lean/WeilConjectures` for this node id: no declaration.

Server validation: scompile.py compiled the final module successfully. The first
compile identified missing scoped `MonObj` notation for the identity point; this
was corrected. The local compiler reported disk space exhaustion, but the wrapper's
server confirmation successfully compiled the file within 60 seconds, with no
errors or unexpected warnings. No live source was modified and no global build ran.

## Second reading by Q141

This is the author's separate self-reading; the dispatcher explicitly forbids
starting other agents. Independent review is performed by the maintainer after
delivery. I reread the node, the module and the definition signatures against
Milne. The initially tempting smooth-only unipotence predicate would omit the
nonsmooth cases and was not used. The geometric embedding condition tests all
algebras, preserving the closed-subgroup meaning. The multiplicative-type predicate
is reused literally. The field-extension equivalences each include both directions.
The separate smooth criterion has the required positive exponent and faithful
representation. Only that criterion has a smoothness hypothesis. The final theorem
quantifies over all A-points, including nilpotent A, so does not merely assert
triviality on geometric points. All definitions are formulas without sorry, and
all theorem proofs are sorry. No node/source fault or disputed statement found.
