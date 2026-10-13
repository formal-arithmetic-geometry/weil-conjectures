## What changed

Added the intermediate theorem `affine_algebra_kinjective_canonical_comparison_identification` and used it to prove `affineAlgebraCounitHomologyComparison_isIso`. The intermediate proof remains a named sorry; the target proof is complete. Added only the imports needed for this reduction.

## Proved and sorry left

Proved `AlgebraicGeometry.affineAlgebraCounitHomologyComparison_isIso`.
Sorry left: `AlgebraicGeometry.affine_algebra_kinjective_canonical_comparison_identification`, node `new-affine-algebra-canonical-comparison-identification`.

## No longer needed

No planned proof dependency beyond the canonical comparison compatibility module was needed directly; the affine cohomology comparison existence route is replaced by the canonical-identification intermediate theorem.

## Where the brief, the DAG or earlier work was wrong

The existing affine cohomology comparison theorem only provides an arbitrary isomorphism and cannot prove invertibility of the specified canonical morphism without an identification step. That identification is therefore split out explicitly.

## New nodes

`new-affine-algebra-canonical-comparison-identification`: canonical affine K-injective comparison identification, in `dag/nodes/sec-picard-framework/new-affine-algebra-canonical-comparison-identification.json`.

## Earlier second reading (a previous round; superseded)

The target proof rewrites the specified comparison by the intermediate equality and obtains `IsIso` from the displayed isomorphism. The new statement is strictly stronger than the target's needed conclusion and is a genuine identification step, with the affine unbounded comparison as its source.

## Second reading by N2

1. **Diff and interfaces.** Compared the delivered target module with the repository version. The theorem signature is byte-for-byte unchanged; the only target-module changes are the proof and a proof-only import. The added canonical-identification module and node are explicitly listed as new.

2. **Compilation and axioms.** Compiled all three sandbox modules successfully with `lcompile.py`. The target proof has no local `sorry`, unsafe declarations, or hollow definitions. The canonical-identification theorem remains the single named split-off `sorry`; probing axioms reports only the permitted base axioms plus `sorryAx` through that open theorem.

3. **Statements and duplication.** The target statement is unchanged and asserts invertibility of the specified canonical morphism. The split-off theorem is a strictly stronger identification/existence statement needed to rewrite that morphism to an isomorphism. Repository and Mathlib searches found no duplicate declaration.

4. **Proof route and pruning.** The target proof uses exactly the split-off canonical-identification theorem and `infer_instance`; the target node's proof and `proof_deps` were updated accordingly. The compatibility construction remains the public definition used in the target statement. No additional imports or nodes are needed directly.

5. **Unit route.** The proof retains the affine canonical-comparison route described by the unit's target node. The split-off node records the affine unbounded comparison source and its required proof dependencies; no unit statement or step was changed.

Changed in this second reading: corrected the target DAG proof and dependency metadata to match the actual Lean proof, and added this review record. No Lean declarations were changed.
