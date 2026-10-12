## What changed

Added the intermediate theorem `bijective_qcqsStrictLocalRestriction_of_formula`, whose proof is left as the strictly smaller transport-and-set-comparison step. The target theorem now obtains `IsIso a` from that bijectivity and `ConcreteCategory.isIso_iff_bijective`.

## Proved and sorry left

The original `isIso_qcqsStrictLocalRestriction_of_formula` is reduced to the bijectivity theorem. The new theorem `bijective_qcqsStrictLocalRestriction_of_formula` remains `sorry`; its node is `lem-weil-pbc-strict-local-module-restriction-bijective`.

## No longer needed

None. Both stated proof-dependency modules remain imported; the new module uses the set pushforward comparison and module/set inverse-image comparison.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the substantial transport argument needed to identify the forgotten module map with the set-valued comparison. This was split into a named intermediate theorem rather than left as an anonymous partial proof.

## New nodes

`lem-weil-pbc-strict-local-module-restriction-bijective` is the strict subset of the original conclusion asserting bijectivity of the underlying function. It is in `dag/nodes/sec-proper-base-change/lem-weil-pbc-strict-local-module-restriction-bijective.json`.

## Earlier second reading (a previous round; superseded)

The intermediate theorem has exactly the same hypotheses and map as the item, with the conclusion reduced to bijectivity of the underlying module hom. The final theorem applies the concrete-category equivalence without changing the target statement. The new node is strictly weaker and is the sole remaining hole.

## Second reading by R3

1. Compared the delivered isomorphism module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only the proof and a proof-only import were added. Verdict: pass.
2. Compiled both delivered modules with `lcompile.py --all`; both compile without errors or warnings. The isomorphism theorem has no `sorry`; the sole remaining `sorry` is the named bijectivity theorem, with its matching node. Verdict: pass.
3. Checked the split-off statement and node. The bijectivity conclusion is strictly weaker than `IsIso a`, retains the same hypotheses, and is exactly the property needed by the concrete-category equivalence. Its source, proof sketch, dependencies, and declaration agree. No hollow definition or forbidden declaration was introduced. Verdict: pass.
4. Checked the proof route and pruning. The isomorphism proof uses the bijectivity theorem and `ConcreteCategory.isIso_iff_bijective`; the unit route remains represented by the bijectivity node and its stated dependencies. No imports were removable: the public imports support the signature and the plain imports support the proof/new theorem. Verdict: pass.
5. Checked DAG agreement and report completeness. Existing node proof and proof dependencies now match the Lean proof; the new node records the remaining hole and its origin. No statement or definition was changed. Verdict: pass.

Changed after this reading: appended this review; no Lean proof or statement changes were needed.
