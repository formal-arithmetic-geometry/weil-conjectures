## What changed

Proved `AlgebraicGeometry.Scheme.exists_isSeparated_overPullbackMap` with its signature
unchanged, by applying the existing closed-immersion descent theorem to the diagonal.
The proof establishes the qcqs hypotheses using Mathlib instances and the quasi-separated
pullback projection. Added a proof-only import of
`Sheaf.AlgebraicGeometry.OverPullbackDiagonalClosedImmersion`.

The new module proves `AlgebraicGeometry.isClosedImmersion_overPullback_diagonal_iff`.
It constructs both directions of the fibre-product comparison isomorphism, checks their
composites and the diagonal compatibility, and cancels the isomorphism in the
closed-immersion property. All files compile locally without warnings.

## Proved and sorry left

Proved the item's sole sorry, `AlgebraicGeometry.Scheme.exists_isSeparated_overPullbackMap`.
The new compatibility theorem is also completely proved. No sorry remains in either
delivery module and none was split off. The target proof uses the existing theorem
`AlgebraicGeometry.exists_isClosedImmersion_stage_of_locallyOfFiniteType` (node
`lem-weil-pbc-descend-closed-immersion`), whose existing sorry is intentionally the next
stage-3 dependency; this delivery does not change that module.

## No longer needed

None. No original imports or planned dependencies were removed. The original diagonal,
locally-finite-type, qcqs, and closed-immersion descent route is retained; Mathlib instances
supply the first three. No unit statement or realized step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The source field of the original node describes the diagonal target once as
`X₀ ×_{S₀} X₀`; the statement and proof steps correctly use `X₀ ×_{Y₀} X₀`.
The Lean proof uses the latter throughout. No statement was changed.
LeanSearch returned Internal Server Error, recorded as unavailable rather than no match.
The local literature directory does not contain the Stacks tex source; the compatibility
proof is an explicit agent-written universal-property proof, not a claim to have read
that source. The existing source citation and original descent route are retained.

## New nodes

`lem-weil-pbc-over-pullback-diagonal-closed-immersion` records the fully proved generic
Over-base-change compatibility theorem. Its statement has no inverse system, compactness,
or finiteness hypotheses, so it is strictly the transport step, not a restatement of
separatedness descent. Both directions and the comparison isomorphism are proved in Lean.
The empty-scheme and identity-base-change cases use the same universal-property proof.
Searched all blueprint nodes via `blueprint_refs.py search` and read
`lemma-nagata-diagonal-base-change`: its Mathlib attachment `diagonal_pullback_fst`
addresses base change along the target, whereas this helper transports an S-morphism
along an arbitrary ambient-base map. No duplicate statement was found.
No change record is needed: all existing declaration signatures are unchanged.

## Second reading by H2

1. Compared the delivered target module with the repository version: the target theorem signature is byte-for-byte unchanged; only its proof and a proof-only import changed. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; there are no errors, warnings, `sorry`s, forbidden declarations, or hollow definitions. `#print axioms` on a scratch copy reports only `propext`, `Classical.choice`, and `Quot.sound` for the helper; the target additionally reports `sorryAx` from the existing open closed-immersion descent dependency, as expected. Verdict: pass.
3. Checked the new compatibility statement against its explicit pullback construction and edge cases (including empty schemes and identity base change); it is true and strictly weaker than separatedness descent, and no duplicate declaration was found in the library. Verdict: pass.
4. The proof follows the shortest available route through the existing closed-immersion descent theorem and the diagonal compatibility helper. The proof-only import is minimal; no old proof dependency or unit step is bypassed. Verdict: pass.
5. Updated DAG proof and proof-dependency records agree with the Lean proof, and the new node contains its source, proof, searches, and Lean declaration record. The unit route and realized steps remain intact. Verdict: pass.

Changed no Lean code or DAG records during second reading; clarified the axiom audit in this report. The independent Loogle search for `"IsSeparated", "pullback"` found only the unrelated topological `IsSeparatedMap.pullback`; repository searches found no duplicate of the new compatibility theorem. The delivery is ready for dry-run and delivery.
