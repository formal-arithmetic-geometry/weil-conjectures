## Worker report

The module `Sheaf.GroupTheory.RationalRankZeroTorsion` states
`AddCommGroup.exists_pos_zsmul_eq_zero_of_rationalRank_eq_zero` with proof `sorry`.
The node's mathematical statement and dependency lists are unchanged. No new
notions, helper declarations, dependency repairs, or statement corrections are needed.

Clause-by-clause correspondence:

- An arbitrary abelian group is `(G : Type u) [AddCommGroup G]`, with explicit
  universe `u`. There is no nontriviality, finite generation, finite-dimensionality,
  or bounded-exponent hypothesis.
- The rational rank in the hypothesis is exactly the dependency's
  `AddCommGroup.rationalRank G`, and rank zero is `(h : rationalRank G = 0)`.
  Reading the dependency source shows
  `Module.rank ℚ (ℚ ⊗[ℤ] G) : Cardinal.{u}`. Its docstring explicitly identifies
  this tensor ordering with `G ⊗[ℤ] ℚ` by the canonical symmetry. It uses the
  canonical rational scalar structure and cardinal dimension, including infinite
  dimensions; it does not use `Module.finrank`.
- “For every g in G” is `∀ g : G`.
- “There is an integer n” is `∃ n : ℤ`.
- “n ≥ 1” is `1 ≤ n`.
- “n g = 0” is `n • g = 0`, the canonical integer scalar action on the additive
  group. The conjunction combines the positive-integer condition and annihilation.
  The existential is inside the quantifier over `g`, so there is no uniform
  annihilator requirement.

Dependency declarations read and used:

- Statement: `Sheaf.GroupTheory.RationalRank`, `AddCommGroup.rationalRank`.
  Its complete signature, body, tensor-ordering explanation and source docstring
  were read in the shared read-only Lean source.
- Proof plan: `Mathlib.Algebra.Module.LocalizedModule.Basic`, `LocalizedModule`,
  `LocalizedModule.mk`, `LocalizedModule.mkLinearMap`, and
  `LocalizedModule.mem_ker_mkLinearMap_iff`, implementing
  `def-weil-pbc-module-localization`.
- Proof plan: `Mathlib.RingTheory.Localization.BaseChange`,
  `IsLocalizedModule.rTensor` and `IsLocalizedModule.map_lTensor`, implementing
  `lem-weil-pbc-localization-tensor-over-base`. Their signatures and surrounding
  scalar/module hypotheses were read in the pinned Mathlib source. The module is
  imported without `public`, and supplies the preceding localization definitions.
- Proof plan: `Mathlib.LinearAlgebra.TensorProduct.Defs` and `.Basic`,
  `TensorProduct`, `TensorProduct.lift`, `TensorProduct.lift.tmul`, and
  `TensorProduct.ext'`, implementing `def-weil-pbc-module-tensor-product`.
  These are already publicly imported by the recorded rational-rank module.

The theorem docstring gives all four node proof steps: cardinal dimension zero
implies zero rationalization by the singleton argument; identify the localization
of the integers at nonzero integers with the rationals; apply tensor-localization
and the explicit unit/symmetry identifications to obtain zero localization of G;
then apply the fraction-kernel criterion and replace the nonzero annihilator by
its absolute value. No step is proved in this stage.

Edge cases checked mathematically: the trivial group and `g = 0` admit `n = 1`;
finite torsion groups satisfy the conclusion; arbitrary torsion groups of
unbounded exponent remain allowed since `n` depends on `g`; `G = ℤ` and `G = ℚ`
have rational rank one and do not satisfy the hypothesis. An infinite free
abelian group has nonzero infinite cardinal rational rank, so it cannot enter
through the false implication “finrank zero implies dimension zero.” The group
universe is unrestricted. No empty index set or characteristic condition occurs.

Searches performed (all through the authorized wrapper or read-only `rg`):

- `msearch.py ... leanfinder`: “An abelian group with zero rational rank,
  dimension of its tensor product with Q, is torsion”. Eight hits included
  `rank_eq_zero_iff_isTorsion`, `IsAddTorsionFree.of_module_rat`, and
  `AddMonoid.isTorsion_iff_isTorsion_int`. None directly states the implication
  from the rational tensor's dimension to integer annihilators in G.
- `msearch.py ... loogle`: `Module.rank, TensorProduct`. Five hits concerned
  `Module.rank_baseChange`, tensor ranks and localization ranks. They give general
  interfaces, not the present statement for arbitrary abelian groups.
- `msearch.py ... grep`:
  `rationalRank|rank_eq_zero_iff_isTorsion|torsion.*tensor|tensor.*torsion`.
  Nine hits, chiefly the rank/torsion lemmas and unrelated geometric torsion
  tensors. The pinned source of `Module.rank_eq_zero_iff_isTorsion` was read:
  it compares the rank and torsion of the same module over the same ring.
  Applying it with integers would require a separate rationalization rank bridge;
  applying it with rationals concerns the tensor module rather than G.
- `msearch.py ... leansearch`: “If the rationalization of an abelian group has
  dimension zero, each element is annihilated by a positive integer”. Eight hits
  included `rank_eq_zero_iff` and the same general torsion APIs; no exact match.
- Read-only `rg` searched rational rank, rank/torsion, and torsion/tensor patterns
  in upstream `WeilConjectures`, shared `lean/Sheaf`, and
  `dag/lean_names_upstream.json`. It found the recorded rational-rank definition
  and its valuation applications, but no statement of this implication.
  Searching upstream `WeilConjectures` for the exact item id found no match.
- Read-only `rg` for the proposed full declaration's basename in Mathlib,
  upstream, side modules, and the upstream name index found no collision.

Source validation: opened the source URL
<https://math.huji.ac.il/~temkin/papers/Stable_Modification.pdf>.
Temkin's §2.1 defines the rational dimension invariant using tensoring with Q;
Proposition 4.3.1, printed p. 28, uses vanishing of that invariant to infer that
the value-group quotient is torsion. This is the general abelian-group inference
stated here. The node's source record mentions p. 27 while the reviewed note and
PDF show printed p. 28; the module cites p. 28. This is a source-page discrepancy,
not a fault in the mathematical statement. No STATEMENT-DISPUTED issue remains.

Validation: the prescribed `scompile.py Q113 lem-trf-rational-rank-zero-torsion`
compiled the delivered file in both sandbox and library module contexts, with
no errors and no warnings. The only theorem body is `by sorry`.

## Second reading by Q113

Author's self-check under the direct-delivery brief; no independent reviewer or
sub-agent was started. Reopened the copied node, delivered module, and recorded
rational-rank dependency. Checked `(G : Type u) [AddCommGroup G]` against the
unrestricted abelian group, the sole hypothesis `h` against cardinal rational
rank zero, and the conclusion's `∀ g`, `∃ n : ℤ`, `1 ≤ n`, and `n • g = 0`
against each corresponding phrase. In particular, the annihilator is positive
and element-dependent; there is no finite rank or uniform exponent restriction.
Confirmed the dependency's symmetric tensor ordering and its canonical rational
module structure give the specified invariant. Checked each of the four proof
steps against the docstring and the proof-dependency imports. No statement
mismatch was found and no node correction was made. The maintainer supplies the
independent review, as specified in the worker brief.
