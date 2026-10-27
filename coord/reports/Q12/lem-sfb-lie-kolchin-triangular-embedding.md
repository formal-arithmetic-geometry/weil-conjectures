## Worker report

The module Sheaf.AlgebraicGeometry.GroupScheme.LieKolchinTriangularEmbedding states
AlgebraicGeometry.lieKolchin_triangular_embedding, with its sole proof `sorry`.
Its docstring gives all seven proof steps of the DAG, including the derived-length
induction, all-algebras eigenspaces, closed finite-index stabilizer, repeated-root
case, fppf descent, faithful representation, and adapted full flag.

Hypothesis and conclusion comparison:

- The field k is `{k : Type u} [Field k]`, with `[IsAlgClosed k]` for algebraic
  closedness. No CharZero or other characteristic assumption occurs.
- J is `Grp (Over (Spec (.of k)))`, the recorded group-scheme notion. Affineness
  is `[IsAffine J.X.left]`; finite type is `[LocallyOfFiniteType J.X.hom]` and
  `[QuasiCompact J.X.hom]` together. Smoothness is `[Smooth J.X.hom]` and
  connectedness is `[ConnectedSpace J.X.left]`, including nonemptiness.
- `hsolv : SolvableGroupStructure.IsSolvable J` is precisely a finite closed
  subnormal series terminating at the trivial group. Each inclusion is closed
  and normal and contains every commutator on every commutative k-algebra.
  This is equivalent to commutativity of each fppf sheaf quotient: locally lift
  quotient sections and their commutator is trivial; conversely commutativity
  puts every commutator in the kernel, which is the represented next subgroup.
  The initial and final group isomorphisms avoid imposing a choice of presentation.
- The positive integer is `∃ (n : ℕ), 0 < n ∧ ...`. The index type is
  `ULift.{u} (Fin n)` to use the existing general-linear scheme over `k : Type u`.
- The homomorphism is `r : J.X ⟶ GeneralLinearGroup ... k` together with
  `IsClosedSubgroupScheme r`. That class includes `IsMonHom r` and the actual
  scheme morphism's `IsClosedImmersion r.left`, rather than injectivity just
  on rational points.
- The target B_n is rendered by its defining equations, not by a second chosen
  model: for every `R : Type u`, `[CommRing R] [Algebra k R]`, every point
  `x : (Spec (.of R)).asOver (Spec (.of k)) ⟶ J.X`, and `i j : Fin n`,
  `j < i` implies that the `(i,j)` matrix entry of
  `GeneralLinearGroup.homMulEquiv ... (x ≫ r)` is zero. This includes the
  universal point R=k[J], so all below-diagonal coordinate functions vanish.
  Thus the coordinate surjection k[GL_n] -> k[J] factors through the quotient
  k[B_n], and the induced map from that quotient remains surjective. This is
  exactly a closed immersion J -> B_n. Conversely any closed immersion into
  B_n, composed with B_n -> GL_n, satisfies the displayed statement.
- The introductory U_n is only contextual notation for the subgroup with all
  diagonal entries one; the node asserts no conclusion about U_n. There is
  accordingly no diagonal-one hypothesis or conclusion in this theorem.

Dependency declarations used and read:

- Mathlib.Algebra.Field.Defs: Field; Mathlib.FieldTheory.IsAlgClosed.Basic:
  IsAlgClosed (splitting of every polynomial, equivalent to roots of each
  nonconstant polynomial).
- Mathlib.CategoryTheory.Monoidal.Grp: Grp, GrpObj; upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs: IsSubgroupScheme,
  IsNormalSubgroupScheme, IsClosedSubgroupScheme, and IsMonHom as documented
  there. Read the complete class signatures and their all-algebras conditions.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType: LocallyOfFiniteType;
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact: QuasiCompact;
  Mathlib.AlgebraicGeometry.Morphisms.Smooth: Smooth;
  Mathlib.Topology.Connected.Basic: ConnectedSpace;
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion.
- def-sc-general-linear-group records Sheaf.AlgebraicGeometry.LinearGroupSchemes,
  which publicly imports the actual upstream
  WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear. Read that
  dependency module and the full upstream signatures and docstrings of
  GeneralLinearGroup and GeneralLinearGroup.homMulEquiv. The upstream GL
  coordinate ring is the determinant localization and homMulEquiv identifies
  all R-points with invertible matrices, naturally in R. No SL construction
  from that module is required for this theorem, and no GL is redefined.
- Sheaf.AlgebraicGeometry.SolvableGroupStructure:
  AlgebraicGeometry.SolvableGroupStructure.IsSolvable, read in full. Added its
  already-landed node def-sfb-solvable-group-structure to stmt_deps as expressly
  permitted by brief-stage2 section 5 (STMT_DEPS MAY GAIN LANDED NODES).
  No new notion, dependency repair, or statement correction is introduced.

The stated proof dependencies are imported privately:
Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry,
Sheaf.AlgebraicGeometry.GroupScheme.SmoothConnectedDerivedSubgroup,
Sheaf.AlgebraicGeometry.GroupScheme.HomomorphismFactorization,
WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced, and
WeilConjectures.Mathlib.RingTheory.Nullstellensatz. The Nullstellensatz node's
lean record has no module, but its closed lean_audit lists the last module.
The eigenspaces-independent, commutative-eigenline, and prescribed-kernel
proof nodes have no Lean statement in the read snapshot, so supply no imports.
They remain named explicitly in the proof docstring. General-linear and
closed-immersion dependencies have public imports because the signature uses them.

Source checked directly: literature/milne-algebraic-groups_iAG2017.pdf,
PDF pages 346--347 = printed pp.334--335, Theorem 16.30; PDF page 337 = printed
p.325, Proposition 16.2(a)--(c). These state trigonalizability without a
characteristic-zero hypothesis and identify it with embedding as an algebraic
subgroup of the upper triangular matrices. No source correction was needed.

Edge cases checked before writing: J trivial is smooth connected solvable and
embeds in GL_1, with the triangular equations empty; n=0 is intentionally
excluded by the node's n>=1. No positive dimension hypothesis excludes that
case. The empty scheme is excluded by ConnectedSpace and a group identity.
For n=1 all invertible one-by-one matrices are upper triangular; the diagonal
is not forced to one. Arbitrary characteristic, including char p dividing a
representation dimension, remains allowed. Nonreduced test algebras are included,
so scheme-theoretic conditions are not reduced to geometric-point conditions.
Test algebras and field share universe u, as required by the upstream GL API;
the coordinate algebra k[J] fits this universe. The universal point detects
exactly the coordinate ideal, so the conclusion is neither weaker nor stronger.

Searches actually run via msearch.py (logged in searches.jsonl):

- leanfinder: "Every smooth connected solvable affine algebraic group over an
  algebraically closed field embeds as a closed subgroup of invertible upper
  triangular matrices". Eight hits: LieModule triangularizability, topological
  SL embeddings and root-system results; no group-scheme theorem.
- loogle: "IsSolvable, Matrix.BlockTriangular, GeneralLinearGroup". Zero hits;
  service reported unknown identifier GeneralLinearGroup (the upstream name).
- grep Mathlib: "LieKolchin|lie_kolchin|triangular.*[Ee]mbed|[Ee]mbed.*triangular".
  Zero hits.
- leansearch: "Lie Kolchin theorem connected solvable affine group scheme upper
  triangular closed immersion". Eight hits: LieModule.IsTriangularizable,
  LieAlgebra.IsSolvable and general closed-immersion facts; no exact theorem.
- rg over lean/WeilConjectures and lean/Sheaf for triangular/Triangular,
  IsSolvable/Solvable, and the item's id: upstream has Lie-algebra and single-map
  triangularization, not this algebraic-group theorem. Project has the usable
  SolvableGroupStructure.IsSolvable and downstream textual citations of this item.
  The existing CharZeroCommutativeUnipotentVectorGroup module uses the same
  all-algebras coordinate form for a unitriangular embedding.
- rg for the proposed declaration name in Mathlib and both project roots found
  no collision. DAG searches found def-sfb-solvable-group-structure, which is
  reused; no new definition node is needed.

No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q12

This is a separate self-check of the finished signature against the full node,
not a claim of independent agent review; the dispatch explicitly prohibits
starting other agents. The maintainer performs the independent delivery review.
Rechecked every binder above against the node: field and algebraic closedness,
group scheme, affine finite type, smooth connected, the full closed normal
series, n positive, a group-scheme closed immersion, and upper triangularity
on all algebra points. Checked that U_n adds no theorem clause and that the
GL_n coordinate formulation is equivalent to the closed B_n target by the
quotient-coordinate argument. No extra characteristic or dimension hypothesis,
no diagonal normalization, and no rational-point-only replacement occurs.
The only added DAG dependency names the already-existing solvability definition.
No mismatch was found and no change to the mathematical statement was needed.
