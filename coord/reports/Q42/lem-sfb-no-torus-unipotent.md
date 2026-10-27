## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.NoTorusUnipotent` states
`AlgebraicGeometry.exists_unipotent_representation_of_no_torus`, with one theorem
and its expected `sorry`. No definitions or additional theorems are introduced.
The natural-language statement, proof and proof dependencies are unchanged.

### Hypotheses and conclusion, clause by clause

| Node clause | Lean rendering |
| --- | --- |
| An algebraically closed field k | `{k : Type u} [Field k] [IsAlgClosed k]` |
| A group scheme over k | `(G : Over (Spec (.of k))) [GrpObj G]` |
| Smooth over k | `[Smooth G.hom]` |
| Connected | `[ConnectedSpace G.left]` |
| Affine | `[IsAffine G.left]` |
| Finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| A rank-r torus subgroup, with r an integer at least zero | `r : ℕ` and `i : (MultiplicativeType.splitTorus k r).X ⟶ G`, with `IsClosedSubgroupScheme i` |
| Every such torus subgroup is trivial | `hNoTorus : ∀ (r : ℕ) (i : (MultiplicativeType.splitTorus k r).X ⟶ G), IsClosedSubgroupScheme i → i = 1` |
| There is an integer m at least one | `∃ (m : ℕ), 1 ≤ m ∧ ...` |
| A homomorphism rho into GL_(m,k) | `∃ rho : G ⟶ GeneralLinearGroup (LinearGroupSchemes.Index.{u} m) k, IsMonHom rho ∧ ...` |
| rho is a closed immersion | `IsClosedImmersion rho.left` |
| For every rational point g in G(k) | `∀ g : (Spec (.of k)).asOver (Spec (.of k)) ⟶ G, ...` |
| There is an integer N at least one | `∃ N : ℕ, 1 ≤ N ∧ ...` |
| (rho(g) - I_m)^N = 0 | `((GeneralLinearGroup.homMulEquiv (LinearGroupSchemes.Index.{u} m) k k (g ≫ rho)).val - 1) ^ N = 0` |

`splitTorus k r` is the existing recursive finite product of the recorded
`StandardGroupSchemes.multiplicative k`, with the terminal group at rank zero.
This uses the node's definition of a torus subgroup (a closed subgroup isomorphic
over k to such a finite product). Given an isomorphism from that product to any
such subgroup, compose with its inclusion. Conversely a closed homomorphism from
the product is a subgroup of precisely this type. For a closed subgroup inclusion,
equality `i = 1` means it factors through the identity section. Because the inclusion
is a monomorphism, every algebra-valued point of its source is the identity, so the
subgroup is the trivial group scheme. This is scheme-theoretic triviality, rather
than triviality of rational points alone.

`GeneralLinearGroup.homMulEquiv` is the existing natural group equivalence from
scheme-valued points to invertible matrices. Its `.val` is the underlying matrix;
`1` in that subtraction is the identity matrix and `0` after exponentiation is the
zero matrix. `LinearGroupSchemes.Index.{u} m` is `ULift.{u} (Fin m)`, so exactly m
rows and columns live in the upstream construction's required field universe.
The exponent may depend on g, exactly as in the node. No conclusion about all
algebras of points or a uniform exponent was added to the theorem statement.

### Dependency declarations used

All recorded statement dependencies and their source declarations/docstrings were
read before writing the statement.

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs.
- `def-weil-algebraic-closure`: `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic
  (the algebraically closed clause of its recorded Mathlib match; no chosen closure
  is needed by this statement).
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `def-weil-connected-scheme`: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj` and `CategoryTheory.IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Grp / Mon; their scheme interpretation is documented
  in the reused WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType /
  QuasiCompact. Finite type is their conjunction, not local finite type alone.
- `def-sc-group-scheme-subgroup`: `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. This includes homomorphism,
  injectivity on all algebra-valued points and closed immersion.
- `def-sc-gm-ga`: `AlgebraicGeometry.StandardGroupSchemes.multiplicative` and
  `multiplicativeGroup`, Sheaf.AlgebraicGeometry.StandardGroupSchemes; used by
  the already-defined product torus.
- `def-sc-general-linear-group`: the recorded module
  Sheaf.AlgebraicGeometry.LinearGroupSchemes reuses the upstream
  `AlgebraicGeometry.GeneralLinearGroup` and `GeneralLinearGroup.homMulEquiv`
  from WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Its recorded
  `LinearGroupSchemes.Index` supplies the finite matrix index.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- `def-sfb-tori-multiplicative-type`: `AlgebraicGeometry.MultiplicativeType.splitTorus`,
  Sheaf.AlgebraicGeometry.ToriMultiplicativeType. This existing, reviewed and landed
  definition node is added to `stmt_deps` to reuse the actual finite-product
  construction, as allowed by the standing brief's landed-node addition rule.
  Its node and module are not modified or duplicated.

`AlgebraicGeometry.IsAffine` is Mathlib's standard affine-scheme predicate from
Mathlib.AlgebraicGeometry.AffineScheme, available through the scheme imports.

All proof dependencies with recorded modules are imported privately, and the
Mathlib matches for properness, finite/affine morphisms, closed immersions and
integral morphisms are available through the listed proof imports. The following
proof dependencies have no Lean attachment yet and hence supply no module to import:
`lem-sfb-solvable-subgroup-flag-realization`,
`lem-sfb-nested-homogeneous-quotient-geometry`,
`lem-sfb-solvable-torus-complements`,
`lem-sfb-geometric-unipotence-unitriangular-embedding`,
`lem-sfb-unipotent-homogeneous-quasiaffine`.
Their exact proof roles, together with all eight steps of the node's proof, are
retained in the theorem docstring. No missing proof dependency is needed to type
this stage-2 statement.

### Source and edge cases

Read the actual Milne PDF at printed p.346 (PDF p.358), Proposition 16.60,
and printed pp.282--283 (PDF pp.294--295), Corollaries 14.6 and 14.12.
The source asserts the no-torus implication for a connected group variety over an
algebraically closed field. Its faithful unipotent representation formulation is
exactly the node's conclusion. The node has already expanded the proof's finite
quotient, smoothness and reducedness details; the module preserves that expansion.

Before writing, checked these cases:

- Rank zero is allowed by `r : ℕ`; the recursive split torus is the trivial group.
- The trivial group G is allowed: m = 1, the identity-section representation, and
  N = 1 meet the conclusion. The theorem does not require G to have positive dimension.
- Nontrivial G_m does not satisfy the hypothesis: its rank-one torus inclusion is
  not the trivial homomorphism. Thus the no-torus condition is not vacuous.
- G_a is compatible with the conclusion via its usual two-by-two unitriangular
  representation, whose difference from the identity squares to zero.
- Both characteristic zero and positive characteristic are allowed. No `CharZero`
  or characteristic exponent assumption occurs. Smoothness is retained, including
  the source's exclusion of nonsmooth phenomena such as mu_p.
- The empty scheme is excluded by the explicit connected-space hypothesis, as in
  the dependency's definition. Connectedness is retained even in characteristic
  zero, where disconnected finite groups would otherwise give counterexamples.
- m = 0 and N = 0 cannot witness the conclusion, because both positive bounds
  are written explicitly. The source universe u is arbitrary, and the finite
  lifted index does not restrict the size of the field or its group scheme.

No statement correction, node fault or STATEMENT-DISPUTED issue was found.

### Searches for existing statements

All searches used the prescribed msearch wrapper or read-only project searches.

- LeanFinder: `A smooth connected affine algebraic group over an algebraically
  closed field with no nontrivial torus has a faithful unipotent matrix representation`.
  Eight hits, including `LieModule.instIsFaithfulMatrixForall`,
  `IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed`,
  `IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed`,
  `LieModule.instIsTriangularizableOfIsAlgClosed`, and
  `Matrix.SpecialLinearGroup.isEmbedding_mapGL`. These concern Lie modules,
  associative rings, representations of finite abstract groups, or topological
  matrix groups; none states the scheme-theoretic no-torus implication.
- Loogle: `"torus", "unipotent"` returned zero hits.
- LeanSearch: `A connected linear algebraic group of torus rank zero is unipotent`.
  Eight hits: `SpecialLinearGroup.center_eq_bot_of_finrank_le_one`,
  `Module.subsingleton_of_rank_zero`, `nilpotencyClass_zero_iff_subsingleton`,
  `LieAlgebra.hasTrivialRadical_iff`,
  `CommGroup.isMulTorsionFree_iff_torsion_eq_bot`, `rank_eq_zero_iff`,
  `Submodule.bot_eq_top_of_rank_eq_zero`, `GrpCat.isZero_iff_subsingleton`.
  None is about algebraic group schemes or their torus subgroups.
- Mathlib grep through msearch: `(torus.*unipotent|unipotent.*torus|no_torus)`:
  zero hits.
- Read-only rg of WeilConjectures and Sheaf for
  `(no.torus|torus.*unipotent|unipotent.*torus|rank.zero.*unipotent)` and the node id.
  No declaration of this theorem. The direct node-id hit in
  GroupScheme/CentralMaximalTorusNilpotent.lean is a proof-docstring reference to
  this still-missing lemma, not its statement. Other matches are the related
  perfect-solvable structure theorem and its consumers.
- Full declaration-name search in WeilConjectures, Sheaf and
  dag/lean_names_upstream.json for `no_torus_unipotent`,
  `exists_unipotent_representation_of_no_torus` and `NoTorusUnipotent`: no collision.
- Concept searches located and reused the existing `splitTorus`, multiplicative
  group, GL scheme and `homMulEquiv`; no new definition node was necessary.

### Validation

The delivered module compiled cleanly through the required scompile.py server
wrapper, including both its sandbox and its library module checks (2.7 s and
3.3 s on the first run). All variables and the universe are explicitly bound,
with `set_option autoImplicit false`. All Lean lines have at most 100 characters.
Only the theorem proof is postponed, with the source and complete natural-language
proof in its docstring. The signature in `lean.statement` is copied verbatim
from the theorem declaration up to `:=`.

## Second reading by Q42

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
