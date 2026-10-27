## Worker report

The module `Sheaf.AlgebraicGeometry.SemisimpleTangentStabilizer` states
`AlgebraicGeometry.exists_semisimple_tangent_stabilizer`, with its sole proof `sorry`.
No definition, instance or other theorem is added. The node's natural-language statement,
proof and proof dependencies are unchanged. Its statement dependencies gain the already landed
definition nodes `def-wf-lie-algebra-derivation` and `def-sc-dual-numbers`.
The dual-number-calculus theorem remains only in proof_deps and a nonpublic proof import.
There are no new nodes, dependency repairs, statement corrections or disputed assertions.

Source read: Milne, Algebraic Groups (2017), printed pp.376–377, especially Proposition 17.76,
its displayed dual-number computation, and Proposition 17.74. The source's smoothness argument
refers to Lemma 13.6; the node expands that argument through its existing semisimple-derivation
zero-smoothness prerequisite. The Lean docstring carries all seven node proof steps, including
representability, descent of group operations, the actual coordinate derivation, eigenspaces,
smoothness, and the tangent-image computation. The theorem does not add perfectness or
characteristic-zero assumptions from Proposition 17.74's Jordan-decomposition statement.

Clause correspondence:

- A field k: `{k : Type u} [Field k]`. The algebraic closure is the arbitrary field
  `(K : Type v) [Field K] [Algebra k K] [IsAlgClosure k K]`; its universe is independent.
- A k-group scheme: `G : Grp (Over (Spec (.of k)))`. Its underlying k-scheme is `G.X`;
  the bundled group object supplies exactly multiplication, inverse and identity.
- Affine: `[IsAffine G.X.left]`; smooth: `[Smooth G.X.hom]`; connected:
  `[ConnectedSpace G.X.left]`; finite type: `[LocallyOfFiniteType G.X.hom]` and
  `[QuasiCompact G.X.hom]`, following the finite-type dependency's recorded convention.
- Identity tangent space with its canonical commutator bracket: `GrpObj.Lie G.X` and `⁅Y,X⁆`.
  This is the existing relative identity tangent module. Its existing
  `GrpObj.lieIdentityTangentEquiv` identifies it with the dependency's
  `schemeTangentSpace` at the identity; `GrpObj.lieEquivTangent` and `tangentPoint` give the
  actual dual-number point. No abstract unrelated Lie algebra is supplied as a hypothesis.
- The positive rank is `(n : ℕ) (hn : 1 ≤ n)`. The finite index type `ULift.{u} (Fin n)`
  is canonically Fin n in the common universe required by the existing general linear group.
- The fixed closed group-scheme immersion is
  `i : G.X ⟶ GeneralLinearGroup (ULift.{u} (Fin n)) k`, with `[IsMonHom i]` and
  `[IsClosedImmersion i.left]`. The actual matrix differential is the existing
  `GeneralLinearGroup.RationalHom.differential i`.
- The vector is `(X : GrpObj.Lie G.X)`. The hypothesis `hX` says there are an invertible
  matrix P over K and diagonal entries d such that P inverse times the entrywise scalar
  extension of di(X) times P equals `Matrix.diagonal d`. This says exactly geometric
  diagonalizability, without requiring eigenvalues in k or choosing a basis of Lie(G).
- Representability by a smooth closed subgroup is the conclusion
  `∃ (C : Grp (Over (Spec (.of k)))) (j : C ⟶ G),
    IsClosedSubgroupScheme j.hom.hom ∧ Smooth C.X.hom ∧ ...`.
  A bundled group homomorphism gives the subgroup inclusion and its actual differential.
  `IsClosedSubgroupScheme` includes injectivity on all algebra-valued points and a closed
  immersion. Affineness and finite type of C follow from that closed immersion into G;
  no additional hypotheses or conclusions are inserted.
- For every commutative k-algebra R, the `Set.range` of `c ↦ c ≫ j.hom.hom` is exactly
  the displayed conjugation-fixed subset of `points G.X R`. Write
  `t_R = points.map G.X (DualNumber.lift
    ⟨(Algebra.ofId k (DualNumber R), DualNumber.eps), DualNumber.eps_mul_eps,
    fun _ ↦ Commute.all _ _⟩) (GrpObj.tangentPoint X)`.
  The lift sends a coefficient a to its structural image and epsilon to epsilon.
  Its source is DualNumber k, its target DualNumber R, and it is bundled over k.
  The two outer factors are the constant lift of g along `TrivSqZeroExt.inlAlgHom k R R`.
  Thus the predicate is `g_lift * t_R * g_lift⁻¹ = t_R`.
  This is the very functor in the node, not only its reduced or field-valued points:
  the landed calculus normalizes `E_k(1 tensor X) = tangentPoint X`, and naturality under
  k → R gives `E_R(1 tensor X) = t_R`. Its conjugation clause says
  `g_lift * t_R * g_lift⁻¹ = E_R(Ad(g)(1 tensor X))`. Injectivity of E_R makes the written
  predicate equivalent to `Ad(g)(1 tensor X) = 1 tensor X` on every R. Tensor symmetry
  identifies Mathlib's R tensor Lie with the node's Lie tensor R.
  The map on points is postcomposition by one scheme morphism, so these bijections onto
  the stabilizer are automatically natural in R. No arbitrary action or map is assumed,
  and no choice from a mere existence theorem defines data.
- The final equality is
  `Set.range (GrpObj.differential j.hom.hom) = {Y : GrpObj.Lie G.X | ⁅Y, X⁆ = 0}`.
  This is precisely the tangent space mapped into g. Equality of these underlying subsets
  expresses the asserted equality of subspaces; the map is canonically linear and the
  bracket is bilinear. The differential is injective for this closed subgroup.
- X = 0 is not excluded. There is no centrality assumption and no restriction on
  characteristic, reduced test algebras, perfectness or algebraic closedness of k.

Dependency declarations read and used:

- `Field`: Mathlib.Algebra.Field.Defs; `IsAlgClosure`: Mathlib.FieldTheory.IsAlgClosed.Basic.
- `CategoryTheory.GrpObj` / `Grp`: Mathlib.CategoryTheory.Monoidal.Grp, specialized to
  `Over (Spec (.of k))`, as recorded by def-sc-group-scheme.
- `Smooth`: Mathlib.AlgebraicGeometry.Morphisms.Smooth; `ConnectedSpace`:
  Mathlib.Topology.Connected.Basic; `LocallyOfFiniteType` and `QuasiCompact`:
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact.
- `schemeTangentSpace`, its additive/module structures and `schemeTangentMap`:
  WeilConjectures.AlgebraicGeometry.SchemeTangentSpace. Their full signatures and
  docstrings were read. The intrinsic identity Lie model is the already existing
  canonically equivalent model, with its bracket owned by def-wf-lie-algebra-derivation:
  `GrpObj.Lie`, base-ring module, `lieEquivTangent`, commutator LieRing/LieAlgebra instances
  in GroupScheme.Lie.Basic / Ring / Bracket; `GrpObj.differential` in Lie.Differential.
- `LieRing`, `LieAlgebra`: Mathlib.Algebra.Lie.Basic; the canonical instance here is the
  upstream group-scheme commutator bracket, not an additional Lie structure parameter.
- `IsClosedImmersion`: Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion.
- def-sc-general-linear-group's recorded module
  Sheaf.AlgebraicGeometry.LinearGroupSchemes explicitly reuses the upstream
  `GeneralLinearGroup` and `homMulEquiv` from GroupScheme.GeneralLinear;
  GroupScheme.GeneralLinear.Lie defines `lieAlgebraEquivMatrix` and the existing
  `RationalHom.differential` used here. Their full definitions/docstrings were read.
- `IsSubgroupScheme`, `IsClosedSubgroupScheme`: the exact recorded
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs declarations.
- `DualNumber`, `DualNumber.eps`, `DualNumber.lift` and `DualNumber.eps_mul_eps`:
  Mathlib.Algebra.DualNumber, owned by def-sc-dual-numbers. The actual lift definition
  and its square-zero/commutation hypotheses were read; no helper is duplicated.
- Proof-only `AffineGroupDualNumberCalculus.Data`, `Compatible`,
  `exists_compatible_calculus`: Sheaf.AlgebraicGeometry.AffineGroupDualNumberCalculus.
  The complete source was read, especially normalize/natural/conjugation/equivariant.
- The proof's affine-spectrum dependency is `Spec` / `Spec.map` from
  Mathlib.AlgebraicGeometry.Scheme. `pullbackSpecIso`, from Mathlib.AlgebraicGeometry.Pullbacks,
  is imported nonpublicly for the proof's affine-product step. The dual-number-calculus
  module is now a nonpublic proof import. Other recorded proof
  modules are public imports because their constructions enter the statement.
  The two unrecorded proof-only statements (affine-group Lie-tangent calculus and
  semisimple-derivation zero-smoothness) supply no missing statement construction here;
  they are retained in proof_deps for stage 3 and cannot yet supply module imports.

Edge cases checked mathematically before writing:

- X = 0: di(0) = 0 is diagonalizable with P = identity and d = 0. Its dual-number point
  is identity over every R, so the stabilizer condition is automatic. Taking C = G gives
  tangent image all of Lie(G), since every [Y,0] vanishes.
- A central X likewise has full tangent centralizer; centrality is not assumed.
- G trivial, and dimension-zero Lie(G), are included with a positive-dimensional faithful
  ambient GL if desired. There is no nonzero-vector or positive Lie-dimension assumption.
- n = 1 is included and its diagonalization condition is the usual scalar one. n = 0
  is excluded by precisely the node's n ≥ 1 assumption, not a stronger rank restriction.
- R = zero ring is allowed: CommRing/Algebra do not imply Nontrivial. Dual numbers and
  points are still defined; conjugation fixes the unique infinitesimal point.
- R nonreduced, in particular dual numbers, is allowed without extra instances, so the
  representability statement sees the full closed subscheme and its tangent space.
- Characteristic 2, arbitrary positive characteristic and imperfect k are admitted. The
  bracket is alternating in the existing LieRing; no division by an integer occurs in
  the signature or the source's expanded eigenvalue argument.
- The closure K may be in an arbitrary independent universe v. Test-algebra universe u
  is the common site universe already used by points and the subgroup-scheme interface;
  it is not an independent smaller universe rendering the condition vacuous.

Searches for an existing identical statement (all msearch calls use Q24 and this item):

- `leanfinder`, query “Centralizer of a semisimple tangent vector in a smooth algebraic
  group is a smooth closed subgroup whose Lie algebra is the bracket centralizer”:
  eight results, concerning manifold Lie algebras, Lie centers and Cartan subalgebras;
  none represents the algebraic-group tangent stabilizer.
- `leansearch`, query “smooth closed subgroup scheme stabilizer semisimple Lie algebra
  tangent vector”: eight results, abstract stabilizers, smooth morphisms and manifold
  invariant vector fields; no matching theorem.
- `loogle`, query `LieAlgebra.ad, GrpObj, Smooth`: zero results, GrpObj not known to the
  remote search index. Retried with `"centralizer", "Smooth"`: successful, zero results.
- `grep`, query `semisimple.*stabilizer|stabilizer.*semisimple|smooth.*centralizer|centralizer.*smooth`:
  zero Mathlib hits. Direct rg of Mathlib LinearAlgebra for diagonalizability found only
  semisimple/triangularizable linear-map material, not the target statement.
- Direct rg of project `lean/WeilConjectures` and `lean/Sheaf` for the item id, the proposed
  theorem name and semisimple stabilizer / smooth centralizer expressions: no duplicate.
  Related results concern torus centralizers or abstract Lie centers. Reading
  AffineGroupDualNumberCalculus and GroupScheme.GeneralLinear.Lie found the canonical
  interfaces used instead of new definitions. No new definition node is needed.

Validation: the initial full statement compiled cleanly through scompile.py, sandbox and
library checks (8.8 s and 2.8 s respectively). After adding the explicit nonpublic affine-product
proof import, all compilation and delivery checks are rerun by the required dry run.


## Repair of returned delivery cbd9b495ef26

H2 was the sole return point. Both occurrences of
`AffineGroupDualNumberCalculus.dualMap (Algebra.ofId k R)` have been replaced by exactly
the requested Mathlib `DualNumber.lift` with structural coefficient map
`Algebra.ofId k (DualNumber R)`, distinguished element `DualNumber.eps`, square-zero proof
`DualNumber.eps_mul_eps`, and commutation proof `fun _ ↦ Commute.all _ _`.
The public import is now Mathlib.Algebra.DualNumber. The calculus module is a nonpublic
proof import. The theorem node lem-sfb-affine-group-dual-number-calculus was removed from
stmt_deps and replaced by the definition node def-sc-dual-numbers, as explicitly requested;
it remains in proof_deps. The existing Lie definition dependency is retained.
The node was compared with current main: current main has no Lean record and its original
eleven stmt_deps; the repair preserves all of its other fields. The previous delivered
signature is retained except for those two canonical map expressions, and lean.statement
was regenerated verbatim from the repaired file. No natural-language statement correction
is involved. The new map has exactly the same action on a + epsilon*b as the old map,
namely the structural images of a and b. Therefore the conjugation subset, including
X = 0, R = 0 and nonreduced test algebras, is unchanged.
Compilation, dry run and delivery below use the repaired module, not the returned head.

The first repair compile diagnosed that IsClosedSubgroupScheme had previously been exposed
through the public calculus import. Added a direct public import of its recorded owning
module WeilConjectures.AlgebraicGeometry.GroupScheme.Defs; the calculus remains private.

Repaired module compiled cleanly through scompile.py: sandbox 3.8 s, library 5.1 s.
The signature matches lean.statement verbatim; maximum line width is 97 characters.

## Second reading by Q24

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
