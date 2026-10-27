## Worker report

The module `Sheaf.AlgebraicGeometry.CharZeroAdjointDifferentialCentralKernel` states
`AlgebraicGeometry.exists_charZero_adjoint_differential_central_kernel`. Its sole theorem
has proof `sorry`. The helper `adjointBasisTangentPoint` is a genuine definition, a finite
ordered product of scaled tangent points. It introduces coordinates for this theorem,
not a replacement tangent space, bracket, differential, group scheme, or centre.

Clause-by-clause reading:

- `k : Type u`, `[Field k]`, `[CharZero k]` give exactly a characteristic-zero field.
- `G : Grp (Over (Spec (.of k)))` is a group scheme, including all of its group axioms.
  `hG : SolvableGroupStructure.IsAlgebraic G` unfolds to `IsAffine G.X.left ∧
  LocallyOfFiniteType G.X.hom ∧ QuasiCompact G.X.hom`: exactly affine finite type.
  Despite the namespace, this predicate imposes no solvability assumption.
- `hsm : Smooth G.X.hom` and `hc : ConnectedSpace G.X.left` give the two remaining
  hypotheses. ConnectedSpace includes nonemptiness.
- `GrpObj.Lie G.X` is the upstream relative tangent space at the identity, implemented
  as the dual of the identity cotangent sheaf. Its equivalence with identity-reducing
  dual-number points is `GrpObj.lieEquiv` followed by
  `GrpObj.infPointsEquivTangentGroup`; `GrpObj.tangentPoint` is their composite.
  This is the identity-point presentation of the recorded `schemeTangentSpace`, not
  an unrelated vector space. The upstream `LieRing` and `LieAlgebra k` instances use
  the mixed group commutator (see GroupScheme/Lie/Bracket.lean, especially its module
  docstring and instances). These supply the bracket in the statement without any
  new choice of bracket. Existence of `n` and the finite `Module.Basis` witnesses
  finite dimensionality; it is a conclusion, not an extra hypothesis.
- `r : G ⟶ Grp.mk (GeneralLinearGroup (ULift (Fin n)) k)` is a morphism of group
  schemes, not an arbitrary map on points. In the existential basis b, GL_n is
  precisely GL(Lie G). The upstream `homMulEquiv` identifies its A-points with
  invertible A-matrices, equivalently Aut_A of A tensor Lie(G).
- The first conjunct specifies the adjoint representation: for every commutative
  k-algebra A, every g and every coordinate vector v, the tangent point associated
  to r(g)v equals c_*(g) t_v c_*(g)^(-1). The helper forms t_v from the actual
  basis vectors: extend k[ε] to A[ε], scale ε by each coordinate, and multiply the
  resulting points. Tangent multiplication is addition, so this is precisely
  the canonical scalar-extension tangent point. Testing all v fixes every matrix
  entry and specifies differentiated conjugation, not an arbitrary representation.
- The second conjunct is dAd_e(X)(Y)=[X,Y]: the upstream
  `GeneralLinearGroup.RationalHom.differential` identifies the differential with
  an endomorphism matrix; `b.equivFun` puts Y and [X,Y] in the same coordinates.
- The third conjunct says N=Z(G) as closed subgroup schemes: the represented image
  of `GrpObj.kerι r.hom.hom` on every A equals
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A`, the exact universal centre
  subfunctor used by the recorded centre theorem. On affine test algebras, equality
  of represented image subfunctors identifies the closed subschemes (test their
  quotient coordinate rings). This retains their scheme structures.
- The final conjunct is the stated consequence: for each x in N(A) and every g in
  G(A), its image commutes with g. No reducedness or nontriviality condition on A
  appears, nor a positivity condition on n.

Dependency declarations read and reused:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, `Grp`, group-object
  homomorphisms and their groups of points; `Field` is Mathlib's existing field class.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`: `IsSubgroupScheme`,
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, and the kernel closedness facts.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `.QuasiCompact`, `.Smooth`:
  `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`; and
  `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `WeilConjectures.AlgebraicGeometry.SchemeTangentSpace`: `schemeTangentSpace`,
  its canonical additive/module structures, and `schemeTangentMap`. The identity
  tangent uses the already-existing equivalent `GrpObj.Lie` presentation, with
  the canonical commutator bracket from `GroupScheme.Lie.Bracket`.
- `Mathlib.Algebra.Lie.Basic`: `LieRing`, `LieAlgebra` and bracket notation.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie.Bracket` (the existing declaration record on `def-wf-lie-algebra-derivation`, `AlgebraicGeometry.GrpObj.lieEquivTangent` and its declarations): the canonical `GrpObj.Lie` tangent presentation, commutator `Bracket`, `LieRing`/`LieAlgebra` instances, `GrpObj.tangentPoint`, and the matrix differential interfaces used in the theorem. This existing node is now explicitly included in `stmt_deps` because the theorem statement uses those declarations directly.
- `Sheaf.AlgebraicGeometry.AffineGroupCentreBaseChange`:
  `exists_affine_group_centre_baseChange`; its recorded
  `ReductiveTorusCentralizer.centralizerPoints` specifies the universal centre.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `affine` for the test objects;
  `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `IsAlgebraic` for affine finite type.
- `Sheaf.AlgebraicGeometry.LinearGroupSchemes` explicitly reuses upstream
  `GeneralLinearGroup`; `WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie`
  supplies `RationalHom.points`, `RationalHom.differential`, and `lieAlgebraEquivMatrix`.
- `WeilConjectures.Mathlib.Algebra.DualNumber`: `scale`, `mapAlgebraMap`; Mathlib
  `TrivSqZeroExt.inlAlgHom` is the actual constant inclusion.
- The existing recorded proof dependencies are imported for stage 3:
  `BialgebraDistribution.finiteOrderConvolutionAndTangentDerivations` in
  `Sheaf.RingTheory.BialgebraDistributionTangentCalculus`;
  `affine_finiteType_algebra_of_field` in `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`;
  `smooth_of_grpObj_of_charZero` in `GroupScheme.Cartier`;
  `GeometricallyConnected.of_connectedSpace_of_section` in the upstream geometrically
  connected module; `Smooth.geometricallyReduced` in the upstream geometrically
  reduced module; `IsClosedImmersion.existsUnique_fac_of_range_subset_range` in
  the upstream closed-immersion module; the affine morphism adjunction and pullback
  spectrum formula are Mathlib imports. The Lie-tangent-calculus and Lie-factorization
  proof nodes have no recorded module, so there is no such module to import yet.

Added statement edges to already-landed nodes `def-sc-general-linear-group`,
`def-sc-gm-ga`, and `def-sfb-solvable-group-structure` for the precise interfaces used.
No new nodes or dependency repair modules, and no statement correction.

Sources checked: local Milne PDF, printed pp.190--196 (especially 10.18--10.24),
pp.33--34 (1.92 and the base-change paragraph). The kernel equality is correctly
identified in the node as an agent corollary rather than an assertion of 10.33 alone.
The latest blueprint is the 20261024 snapshot; its unit route is unchanged.

Edge cases checked by mathematical reading: n=0 uses an empty basis, empty matrix,
and empty list product equal to the identity; the trivial group is included. For
G_a and G_m, conjugation and the Lie bracket are trivial and the kernel is G. For
GL_2, conjugation differentiates to XY-YX with the stated sign. For SL_n, the
finite central subgroup is retained by equality of subfunctors. Nonreduced algebras
such as k[δ]/δ² are allowed; also A=0 is allowed by CommRing, with no Field or
Nontrivial A binder. All test algebras and G live in the common universe u,
matching the recorded centre and group-scheme conventions; ULift allows n=0
and an arbitrary ambient field universe. No auto-bound variables or universes.

Searches (2026-10-24):

- msearch.py leanfinder, query “Differential of the adjoint representation of a
  connected algebraic group is the Lie bracket and the kernel equals the scheme
  centre in characteristic zero”: eight hits, all on Lie-algebra ad kernels,
  trace forms or faithfulness, none the group-scheme theorem.
- msearch.py loogle, query `LieAlgebra.ad, Subgroup.center`: no hits.
- msearch.py grep, query `adjoint|Adjoint` in AlgebraicGeometry: 13 unrelated
  adjunction hits; no adjoint representation or kernel theorem.
- rg on the project's WeilConjectures and Sheaf trees, queries `adjoint`,
  `Adjoint`, `conjugation`, `LieAlgebra`, and the full node id: no existing
  theorem with the complete statement. Found and read the canonical upstream
  Lie and differential modules and the separate AdjointKernelPoints definition;
  the latter is not redefined and is unnecessary for the chosen actual-kernel statement.
- Read the existing AdjointKernelCentralQuotientUnipotent theorem: it is over
  an algebraically closed field and asserts a unipotent quotient, not this theorem.

Validation: scompile.py compiled the delivered module both as the sandbox probe
and with its library name, with no errors or warnings. Every definition has real
construction data and the only postponed proof belongs to the item theorem.

## Second reading by Q143

I reread the node and the full module against the clauses above, with particular
attention to the sign of the commutator, the existential finite basis, and universal
algebra quantification. No mathematical mismatch was found. The imported general
linear node uses the upstream GL construction even though its primary declaration
is specialLinear; the module's note and public import state this explicitly.
This is the worker's rereading, not a claim of an independent second agent review:
the dispatcher explicitly prohibits starting agents and assigns the independent
review to the maintainer after delivery.

## Returned delivery repair

The maintainer returned head `02741c02b381` for H2: the owning node
`def-wf-lie-algebra-derivation` was missing from the statement dependency closure.
Added that already-recorded node directly to `stmt_deps`, alongside the three
previously added existing definitions. Read its current `lean` and `lean_audit`
records: they own the Lie module and commutator structures, dual-number tangent
interface, and rational matrix action/differential used here. The dependency list
above now documents that ownership. The Lean module is unchanged, as requested.
The sandbox node was compared with the current main node; its delivery changes
remain confined to `lean` and the four added existing statement dependencies.
The minor H11 observation remains accurately disclosed in the second-reading
section: no independent worker review is claimed; the dispatcher forbids spawning
agents and the maintainer supplies the independent review.
