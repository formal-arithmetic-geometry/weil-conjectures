## Worker report

The delivery states `AlgebraicGeometry.connected_group_dimension_two_solvable` in
`Sheaf.AlgebraicGeometry.GroupScheme.ConnectedGroupDimensionTwoSolvable`. Its only
proof is `by sorry`; no definitions or helper theorems are introduced. The node is
unchanged except for its `lean` record.

Source checked directly: Milne, *Algebraic Groups* (2017), Corollary 17.27,
printed p.360, and the standing connected-group-variety/algebraically-closed-field
hypotheses of Section 17(b), printed p.353. The source proof treats the three
possible Borel dimensions 0, 1, 2, without a characteristic restriction. The
node's four expanded proof steps, including their dependency names, are in the
Lean declaration docstring.

Clause-by-clause translation:

| Node clause | Lean |
| --- | --- |
| k is a field | `{k : Type u} [Field k]` |
| k is algebraically closed | `[IsAlgClosed k]` |
| G is a k-group scheme | `(G : Over (Spec (.of k))) [GrpObj G]` |
| G is smooth over k | `[Smooth G.hom]` |
| G is connected | `[ConnectedSpace G.left]` |
| G is affine | `[IsAffine G.left]` |
| G is of finite type over k | `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]` |
| Krull dimension of the underlying space is at most two | `hdim : topologicalKrullDim G.left ≤ 2` |
| Scheme-theoretic derived-series solvability | `IsSolvableGroupScheme G` |
| Some integer n ≥ 0 | The existing definition quantifies `∃ n : ℕ` |
| D⁰G = G, DⁿG = 1 for some n | `GroupSchemeDerivedLength G n` recurses from terminality at zero through a derived-subgroup inclusion at each successor |
| Each successor is the smallest closed subgroup containing the commutator | `IsDerivedGroupScheme` requires closedness, factorization of `groupSchemeCommutator`, and factorization into every other such closed subgroup |
| No characteristic restriction | No `CharZero`, `CharP`, or perfectness binder is imposed |

The conclusion uses the recorded definition, not abstract solvability of k-points.
In particular terminality is the trivial scheme over k and does not discard
nonreduced subgroup structure. All variables and the universe u are explicit.
The numeric bound is interpreted in `WithBot ℕ∞`, the actual codomain of
`topologicalKrullDim`.

Statement dependencies read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field` (via public imports).
- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed` (via Semisimple).
  The algebraic-closure node's match explicitly records this predicate for the
  algebraically closed clause; constructing an algebraic closure is unnecessary.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, on `Over (Spec k)`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsSubgroupScheme`, `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, read in
  full; `IsClosedSubgroupScheme` is used inside the existing derived subgroup.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Mathlib.Topology.KrullDimension`: `topologicalKrullDim`.
- `Sheaf.AlgebraicGeometry.GroupScheme.Semisimple`: `groupSchemeCommutator`,
  `IsDerivedGroupScheme`, `GroupSchemeDerivedLength`, `IsSolvableGroupScheme`.
  The declarations and docstrings were read, including the terminal base case
  and the universal minimality clause for the derived subgroup.

The module publicly imports Semisimple and KrullDimension, which expose the
statement vocabulary. Existing proof-dependency modules are plain imports:
Borel (`IsBorelGroupScheme`), PerfectSolvableUnipotentTorus
(`perfect_solvable_unipotent_torus`), AffineNormalQuotientGeometry
(`affine_normal_quotient_geometry`), upstream GroupScheme.Separated
(`GrpObj.isSeparated_hom`), and StandardGroupSchemes. The proof-only nodes
`lem-sfb-solvable-normal-subgroup-products`,
`lem-sfb-homogeneous-quotient-krull-dimension`,
`lem-sfb-perfect-unipotent-additive-series`, and
`lem-sfb-nilpotent-borel-equals-group` have no recorded Lean declaration in the
read snapshot, so no module for them is imported. None supplies missing
vocabulary for this statement.

Edge cases checked mathematically before writing:

- The trivial group is included: dimension zero, derived length zero.
- G_a and G_m have dimension one and are commutative, so the derived series
  terminates after at most one step.
- Products of these groups and the noncommutative affine group G_a ⋊ G_m have
  dimension two and are solvable; the conclusion does not assert commutativity
  or nilpotence of every group of dimension two.
- SL₂ has dimension three, so the dimension bound excludes this nonsolvable
  test case in every characteristic, including characteristic two.
- The empty scheme cannot satisfy ConnectedSpace; no dimension-minus-infinity
  loophole is introduced. Nonreduced infinitesimal groups such as α_p fail
  smoothness and do not justify dropping that hypothesis.
- Algebraically closed fields of positive characteristic are included exactly
  as characteristic-zero fields are; no field-extension test uses an unrelated
  smaller universe.

Searches for an existing statement (2026-10-24 UTC):

- `msearch.py ... leanfinder "Every smooth connected affine algebraic group of
  dimension at most two over an algebraically closed field is solvable"`:
  eight hits, including `CommGroup.isSolvable`, `IsSolvable`, and
  `isSolvable_def`. These concern abstract groups and do not state the
  algebraic-group dimension theorem.
- `msearch.py ... loogle "IsSolvableGroupScheme, topologicalKrullDim"`:
  zero hits, unknown identifier IsSolvableGroupScheme in Mathlib's index.
- `msearch.py ... grep "solvab|Borel" AlgebraicGeometry`: zero Mathlib hits.
- `rg` on `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for solvability/dimension combinations and the
  proposed declaration name: no existing statement. Broader solvability/Borel
  searches found the reused Semisimple and Borel definitions and statements
  referencing this mathematical input, not a duplicate low-dimension theorem.
- Search of `lean/WeilConjectures` for the exact node id: no occurrence.

Validation: the prescribed `scompile.py` compiled the delivered file successfully
both as its sandbox module and with its actual library module name (5.2 s and
2.7 s respectively), with no errors or warnings. No statement fault, correction,
new node, or dependency-interface repair was needed.

## Second reading by Q88

A second pass compared the unchanged JSON statement and the delivered Lean file,
then unfolded the existing solvability definition in the read-only source.
Field and algebraic closure match the first two binders; the group is an object
of Over Spec k with its actual group-object structure. Smoothness, connectedness,
affineness, and both components of finite type each have their own binder. The
dimension hypothesis uses the underlying topological space and includes equality
at two. The conclusion expands to a finite scheme-theoretic derived series whose
zero case is terminality; the minimality clause is not replaced by containment
of commutators alone. No characteristic or commutativity hypothesis was added,
and the trivial group is retained. No mismatch was found and no statement was
changed. This is a second pass by the same dispatcher worker, not a claim of an
independent agent review: the brief forbids starting other agents. Independent
review is the maintainer's delivery review.
