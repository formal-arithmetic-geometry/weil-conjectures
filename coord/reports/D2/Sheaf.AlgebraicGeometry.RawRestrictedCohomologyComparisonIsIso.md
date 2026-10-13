## What changed

Compiled the previously blocked dependency in the sandbox and reduced the target
to a separate derived Yoneda evaluation theorem. The target proof composes that
evaluation isomorphism with the explicit `RawRestrictedComparison.shiftIso`.

## Proved and sorry left

The target declaration `isIso_rawRestrictedCohomologyComparison` is proved by
composition of isomorphisms. One strictly smaller theorem remains sorry:
`isIso_rawRestrictedCohomologyComparisonEvaluation`, the evaluation factor before
the shift identification.

## No longer needed

The target proof no longer directly uses the old plan's nodes
`def-weil-pbc-etale-cohomology`, `def-weil-pbc-inverse-image`,
`def-weil-pbc-sheafification`, `lem-weil-pbc-dplus-injective-representative`,
`lem-weil-pbc-etale-restriction-injectives`, or
`lem-weil-pbc-kinjective-hom-derived`; these were removed from the target
node's `proof_deps`. No import is removed from the target module: the map module
still supplies all public definitions used by its statement and proof.

## Where the brief, the DAG or earlier work was wrong

The earlier BLOCKED result was caused only by the shared compiled library lacking
`RawRestrictedCohomologyComparisonMap.olean`; compiling the dependency in the
sandbox with `lcompile.py --all` resolves that tool-state failure. The full
derived Yoneda calculation is not available as an existing declaration, so it is
represented by the strictly smaller evaluation theorem below.

## New nodes

Added `lem-sbc-raw-restricted-cohomology-comparison-evaluation-is-iso`, matching
`isIso_rawRestrictedCohomologyComparisonEvaluation` in the new module
`Sheaf.AlgebraicGeometry.RawRestrictedCohomologyComparisonEvaluationIsIso`.

## Second reading by D2

1. **Visible changes.** Compared the delivered target module with the repository
version. The declaration signature is byte-for-byte unchanged; the only target
change is its proof, and the new evaluation theorem has its own module and node.
2. **Compilation and axioms.** Compiled all three sandbox modules with
`lcompile.py --all`; compilation succeeds. The target has no new `sorry`, `axiom`,
`unsafe`, `opaque`, `extern`, or `implemented_by`. The evaluation theorem is the
single explicitly split `sorry`, documented above with its source and node.
3. **Statements and searches.** Checked the evaluation statement against the map
definitions and the Stacks tags cited in its docstring. It is a strict
factorization of the target (before `shiftIso`), not a restatement. The recorded
searches found no existing theorem matching it.
4. **Pruning.** The target proof uses only the map module and the split evaluation
theorem; the former's `shiftIso` supplies the second isomorphism. The obsolete
proof-dependency nodes are removed from the target node below.
5. **Unit route.** The target remains the realization of the same unit statement;
the proof is a below-unit reduction through the explicit comparison map and its
evaluation factor.

Changed the target node's proof and `proof_deps` to record this composition, and
added the split evaluation module/node. No existing declaration statement or
definition was changed.
