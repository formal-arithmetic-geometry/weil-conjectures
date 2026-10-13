## What changed

Replaced the proof of `Algebra.FiniteType.exists_finite_subalgebra_away_surjective`,
keeping its original signature and docstring byte for byte. The proof obtains finite
algebra generators, uses the scaled-generator finite-subalgebra construction, extends
scaled membership to all elements by `Algebra.adjoin_induction`, and applies Mathlib's
`IsLocalization.Away.map_surjective_iff`.

The new proof-only import is
`Sheaf.RingTheory.NoetherNormalizationOverDomainSurjectiveCore`; `Mathlib.Tactic.Ring`
is also imported without `public`. The new core module publicly imports only evaluation
and module-finiteness definitions needed by its statement.

## Proved and sorry left

Closed the original hole in
`Algebra.FiniteType.exists_finite_subalgebra_away_surjective` by a genuine reduction.
Added one named hole:
`Algebra.FiniteType.exists_finite_subalgebra_away_core`, node
`new-noether-normalization-over-domain-surjective-core`. It constructs a finite
subalgebra containing a common nonzero multiple of each of finitely many specified
generators; it asserts neither clearing for all elements nor localization surjectivity.
Its docstring supplies a complete natural-language proof following Stacks 07NA.

This is a decomposition: one original hole closed, one new hole added, net zero.
The target still depends on `sorryAx` through the construction theorem and is not an
axiom-free result. All-elements denominator clearing and localization surjectivity
are now proved rather than split off. The first worker's undelivered
`exists_clearing_element_for_core` and
`localization_away_map_surjective_of_clearing` holes and nodes were removed.
No definitions or arbitrary witnesses chosen in definitions were added.

## No longer needed

No original imports were removed and no established module is pruned.
The old proof dependency `lem-weil-pbc-noether-normalization-over-domain` is no longer
used by this node: it is the caller of this theorem, so using it here would be circular.
The repaired construction plan retains the field-normalization, finite-is-integral,
and finite-integral-generators nodes. The unit's realized route is preserved.

The first worker's undelivered clearing and localization nodes are not needed.
The proposed core's localization import was removed; its finite-type import was
replaced with the narrower module-finiteness definitions import.

## Where the brief, the DAG or earlier work was wrong

The first worker's clearing statement was false: take R = Q, S = Q[X], d = 0,
and S' the constants. Evaluation of polynomials in zero variables is injective,
and S' is finite over its range, but no nonzero rational f and exponent n makes
f^n X constant. Thus the originally stated core data do not justify the claimed
clearing theorem. This false undelivered statement was removed, rather than retained
as a sorry or weakened on behalf of an existing library user.

The first worker's localization hole duplicated Mathlib's
`IsLocalization.Away.map_surjective_iff`. Its new node statements were only declaration
names, its source proofs were incomplete, and it had not updated the original node's
proof dependencies. These were corrected or removed.

Mathlib has field Noether normalization and upstream has
`Algebra.FiniteType.exists_finite_aeval_away` in
`WeilConjectures.Mathlib.RingTheory.NoetherNormalization`. The latter supplies
finiteness after localization, not the required finite subalgebra before localization.
It may assist the remaining construction proof, but is not an exact match. The source
proof was read at https://stacks.math.columbia.edu/tag/07NA because the literature
checkout is absent on this machine. LeanSearch returned an internal server error;
LeanFinder, Loogle and grep searches actually ran and their records are in searches.jsonl.

## New nodes

`new-noether-normalization-over-domain-surjective-core` is the finite-subalgebra
construction portion of Stacks 07NA, up to and including scaled-generator membership.
Its complete statement, source, proof plan, dependencies, actual searches and verbatim
Lean signature are recorded. The original surjectivity node now records this construction,
the proved adjoin-induction argument, and Mathlib's surjectivity criterion.
There are no change records: no existing statement or definition changed.

## Second reading by F3

1. Compared the delivered target module with the repository using diff and checked the
existing theorem signature byte for byte. Verdict: unchanged; only proof imports and
proof body changed. The core theorem is new and undelivered, so its repair changes no
existing interface.
2. Compiled both modules in import order through lcompile.py, without errors or warnings.
Checked for forbidden declarations and for unnamed or definition holes. Verdict: one
named theorem hole, none elsewhere. A scratch `#print axioms` check confirms only
standard axioms and the explicitly reported `sorryAx` from the core construction.
3. Tested the original split on the rational polynomial counterexample and removed its
false clearing claim. Checked the replacement construction against Stacks 07NA, including
empty generator sets, d = 0, non-domain S and possible R-torsion in S. The proof clears
localization-zero relations as well as coefficient denominators. An empty generator
set allows S' = S and f = 1; for S = R[X], coordinates can include X. Verdict: the
remaining statement is true and strictly the construction portion of the argument.
Searched LeanFinder, Loogle, Mathlib and upstream/library sources independently;
used the existing Mathlib localization result instead of leaving a duplicate hole.
4. Reviewed the proof from the target downward. All-elements clearing is proved by
adjoin induction and localization surjectivity is an existing Mathlib lemma. Imports
are used; proof-only imports are private to the module. Read dag/units/sk-thm-p1.json:
this auxiliary node is not itself a realized unit step and none of the unit's realized
nodes or routes were bypassed. Verdict: route preserved; no established module pruned.
5. Compared the node records against the final Lean proof. Updated the original node's
proof, proof_deps and proof_origin; replaced the new core's placeholder statement and
incomplete proof/search records; removed the two unused undelivered nodes. Verdict:
records agree with the reduction and the single remaining construction hole.

Changes by the second reader: removed a false split; proved clearing and localization
surjectivity; reduced three proposed holes to one construction hole; restored the original
target docstring; narrowed new imports; repaired the nodes and the hole accounting.
