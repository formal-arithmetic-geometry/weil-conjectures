## What changed

Proved `CategoryTheory.truncation_raw_exact` in
`Sheaf.CategoryTheory.TruncationRawExact` without changing its signature, universes,
visibility, definitions, or public imports. The proof maps the canonical distinguished
truncation triangle through the unbounded K-injective right derived functor, applies
Mathlib's three homology exactness lemmas, and transports the exact short complexes
through `TruncationCouple.bridgeIso`. Six private helpers are proved: exact transport,
naturality under one or two index equalities, naturality with a common final target,
and the two final zero-index/equality-cast adjustments.

Updated `lem-sp-truncation-raw-exact` only in `proof`, `proof_deps`, and `proof_origin`
to record the implemented argument. The route within the blueprint unit is unchanged.
The existing closed node `lem-pc-right-derived-functor-triangulated` records the actual
unbounded functor instance used by the proof; its module is already publicly imported
by `TruncationCouple`.

Validation: the full module compiles cleanly through `lcompile.py`. All integer
indices remain unrestricted; the equality transport helpers prove the required
identities by equality elimination, so negative indices and zero objects require no
extra hypotheses. No new data is chosen from an existence statement; the existing
canonical boundary choice is used unchanged.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.truncation_raw_exact`
(`lem-sp-truncation-raw-exact`). Added 0 holes and split off 0 statements.
Every private helper is fully proved. There are no `sorry`s left in the delivered
module and no new modules. The theorem still relies on the existing statements used
by the truncation construction, particularly `TruncationCouple.existsUnique_boundary`;
this delivery does not claim that its entire dependency closure is axiom-free.

## No longer needed

Removed the proof-only import
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus`.
Removed `lem-weil-pbc-derived-direct-image-triangulated` from this node's proof
dependencies: it supplies the bounded-below right derived functor, whereas the actual
maps use the unbounded K-injective functor. That node and module are unnecessary for
this proof; other target paths may still need them.

Kept `def-sp-truncation-couple` and `lem-sf-derived-homology-long-exact`. No other
planned node or module is pruned. No public import was removed.

## Where the brief, the DAG or earlier work was wrong

The previous node cited the bounded-below derived-functor triangulated instance even
though `TruncationCouple.derivedTriangle` uses `F.rightDerivedFunctor` on unbounded
derived categories. Replaced that citation with the existing closed node for the
unbounded functor, `lem-pc-right-derived-functor-triangulated`.

The raw theorem is true with its original interface; no statement correction or
forced adaptation was needed. The checked-out literature directory has citation
metadata but not the blueprint/Stacks texts named by the node. The existing node
and declaration docstrings supplied the proof plan; the actual proof uses the read
Mathlib and project declarations rather than any newly asserted sourced lemma.

## Second reading by S3

1. **Statements and interfaces.** Compared the delivered module with the repository version. The theorem signature, universes, visibility, definitions, and public imports are unchanged; only the proof and its proof-only import changed. Verdict: pass.

2. **Proof and axioms.** Compiled `Sheaf.CategoryTheory.TruncationRawExact` with `lcompile.py`. The file has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; all six private helpers and `CategoryTheory.truncation_raw_exact` have explicit proofs. Verdict: pass.

3. **New or split statements.** No statements were split off and no new nodes or modules were added. The private helpers are strictly internal transport lemmas, not restatements of the target. Verdict: pass.

4. **Pruning and route.** The proof uses the canonical truncation triangle, the unbounded right-derived-functor triangulated instance, Mathlib homology exactness, and bridge-isomorphism transport. The obsolete bounded-below proof-only import and dependency were removed; the unit route through the truncation couple remains. Verdict: pass.

5. **DAG agreement.** Updated `lem-sp-truncation-raw-exact` to record the actual unbounded triangulated-functor dependency and implemented proof route. Its statement is unchanged, and no unit realization was altered. Verdict: pass.

Changed only the delivered proof, its proof-only import, the node's proof metadata, and this report. No forced adaptations or statement changes were needed.
