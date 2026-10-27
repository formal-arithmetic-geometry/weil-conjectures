## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.RankOneAdjointProjectiveLinear`
states `AlgebraicGeometry.rankOne_adjoint_projectiveLinear`, with `sorry` as its
only proof. It defines no new object and chooses no PGL representative from an
existence theorem. Source read: Milne, Algebraic Groups (2017), Theorem 20.16,
printed pp.412–413, and Theorem 20.22, printed p.415, including the surrounding
reductive semisimple-rank-one convention and the scheme-theoretic kernel argument.

Hypothesis and clause correspondence:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
  `u` is declared explicitly. There is no characteristic hypothesis.
- The affine finite-type F-group scheme is `G : Grp (Over (Spec (.of F)))`.
  `hG : ReductiveTorusCentralizer.IsReductive G` supplies the node's reductivity,
  including `IsAlgebraic G` (affine, locally finite type, quasi-compact), smoothness,
  geometric connectedness and trivial smooth connected normal unipotent radical.
- The largest smooth connected solvable normal subgroup and its quotient appear
  in the existing `RankOneRoots.HasSemisimpleRankOne G`. Its definition quantifies
  over `R`, `Q`, their inclusion and quotient map; it requires a closed normal
  inclusion, smoothness, connectedness, `IsSolvableGroupScheme R.X`, and the
  factorization of every smooth connected solvable closed normal subgroup through
  R. `IsSolvableGroupScheme` is termination of the scheme-theoretic derived series,
  not solvability of F-valued points. The represented quotient is the recorded
  `SolvableGroupStructure.IsFppfQuotient`; it is an fppf cover with the specified
  scheme-theoretic kernel, hence represents the fppf coset sheaf.
- That same rank-one predicate requires every maximal torus of Q to satisfy
  `topologicalKrullDim S.X.left = 1`. It also records existence of a maximal torus,
  which holds for the affine finite-type quotient here by the existing maximal
  torus existence theorem; this does not discard any case of the node.
- PGL2 is `P`, together with `π`, `j`, and
  `hP : ProjectiveMatrixCentralCover.Presentation F 2 (Nat.le_refl 2) P π j`.
  This is the exact recorded projective-matrix central-cover presentation of
  the scalar quotient of GL2. Its universal property is for the fpqc sheaf
  quotient on all test schemes. This is also the fppf quotient: GL2 → P is a
  smooth Gm-torsor, so lifts exist fppf locally. The node already identifies
  PGL2 by this dependency. Arbitrary presentations are parameters, not new
  mathematical assumptions on G; the dependency's existence theorem supplies one.
- The conclusion quantifies `Z`, `i : Z ⟶ G`, and `q : G ⟶ P`. Bundled morphisms
  are homomorphisms of F-group schemes. `IsClosedSubgroupScheme i.hom.hom`
  makes Z a genuine closed subgroup, retaining its scheme structure.
- The full centre is the equality of the image of Z(A) with
  `ReductiveTorusCentralizer.centralizerPoints (𝟙 G) A` for every commutative
  F-algebra A. Unfolding the latter tests commutation with every G(B)-point
  after every F-algebra map A → B. Neither A nor B is required to be reduced.
- Faithful flatness is `q.hom.hom.left.appTop.hom.FaithfullyFlat`, precisely the
  coordinate-ring meaning specified by the quotient dependency.
- `IsFppfGroupQuotient i q` includes the pullback square of q and the identity
  section, so the scheme-theoretic kernel is exactly this Z. It also retains
  the local-surjection, torsor and fppf sheafification universal properties.
  Thus P itself represents G/Z(G); this clause expresses the node's quotient
  conclusion, with the same map q.
- The final universal quantifier says any other represented fppf quotient
  `p : G ⟶ Q` by this centre has `e : Q ≅ P` with `p ≫ e.hom = q`. This is the
  presentation-independent spelling of G/Z(G) ≅ PGL2 and fixes the quotient map.

Dependency declarations read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (line 180).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (line 62), and
  `IsAlgClosure` (line 264); `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`:
  `AlgebraicClosure` (line 127). Only algebraic closedness of F is assumed.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, bundled group
  morphisms; `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, and
  the existing kernel conventions.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `IsMaximalTorus`, `centralizerPoints`.
- `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`:
  `IsFppfGroupQuotient`, with its kernel, torsor and sheaf universal-property
  clauses, and `affine_normal_quotient_geometry`.
- `Sheaf.AlgebraicGeometry.ProjectiveMatrixCentralCover`:
  `ProjectiveMatrixCentralCover.Presentation`, `scalar`, `exists_presentation`;
  it reuses the actual GL2, SL2 and roots-of-unity schemes.
- `Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces`:
  `RankOneRoots.HasSemisimpleRankOne`, read in full. This landed definition is
  added as a statement dependency; it already supplies exactly the radical and
  rank-one notion needed here. Its solvability comes from
  `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`:
  `AlgebraicGeometry.IsSolvableGroupScheme`. No dependency record is repaired.

The module imports all currently recorded proof-dependency modules, privately
unless also needed for the statement. The currently unstated proof nodes
`lem-sfb-rank-one-opposite-borel-intersection`, `lem-sfb-rank-one-flag-curve`,
`lem-sfb-projective-frames-pgl`, `lem-sfb-pgl2-proper-connected-subgroup-solvable`,
`lem-sfb-solvable-proper-fixed-point`, `lem-sfb-torus-normalizer-borel-transitivity`,
`lem-sfb-split-torus-subgroups-diagonalizable`, and
`lem-sfb-faithfully-flat-group-quotient-universal` supply no module to import yet.
Their proof steps remain explicitly described in the theorem docstring. The
Mathlib faithfully-flat injection and spectrum-surjectivity leaves share
`Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra`.

Edge cases checked mathematically before accepting the signature: SL2 has full
kernel μ2, including nonreduced μ2 in characteristic two; GL2 has scalar Gm
kernel; PGL2 has trivial centre; products with any central torus retain semisimple
rank one and their larger centre. A torus and the trivial group have semisimple
rank zero and do not satisfy the rank-one hypothesis. The group scheme has its
identity section, so it cannot be empty. Algebra-valued centre tests include the
zero ring and dual-number rings; no reducedness, separability of the central
isogeny, or characteristic-zero assumption is introduced. All F-algebras and
schemes use the existing universe-u interfaces, so polynomial and coordinate
algebras are included; no smaller test universe is imposed.

Searches actually run:

- `msearch.py leanfinder`: “A reductive affine algebraic group of semisimple rank
  one modulo its scheme theoretic center is the projective general linear group
  PGL2”. Eight hits, concerning abstract matrix SL/PSL groups and their centres;
  none is the group-scheme theorem. Those abstract point quotients do not retain
  infinitesimal kernels and are not substituted for PGL2 here.
- `msearch.py loogle`: `"ProjectiveGeneralLinearGroup"`. Zero hits.
- `msearch.py grep`: `PGL|semisimpleRank|rank.one.*adjoint` in `AlgebraicGeometry`.
  Three unrelated gluing matches; no matching theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `rankOne_adjoint_projectiveLinear`, `rankOneAdjoint`, `PGL`, `IsSolvable`,
  `HasSemisimpleRankOne`, and radical/centre spellings; upstream-name-index
  search for the proposed theorem name; exact item-id `grep -rn` upstream.
  No existing theorem matches the item. The project search did locate the
  reusable rank-one, centre and PGL presentation interfaces described above.
- Read the definition-node DAG entry `def-sfb-rank-one-root-interfaces` to
  establish ownership of the reused rank-one predicate. No new node is needed.

No statement correction, disputed statement, new definition node, dependency
module, proved theorem, or hollow definition is part of this delivery. Apart
from `lean`, the item only gains the already landed rank-one definition in
`stmt_deps`; its natural-language statement and proof remain unchanged.

Validation: `scompile.py Q96 lem-sfb-rank-one-adjoint-projective-linear`
compiled the delivered file both in its sandbox check and under its final module
name with exit code 0 and no warnings. The current server source of
`Sheaf.AlgebraicGeometry.GroupScheme.RankOneRootInterfaces` was also read with
`scompile.py --source` and agrees with the signature used here.

## Second reading by Q96

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
