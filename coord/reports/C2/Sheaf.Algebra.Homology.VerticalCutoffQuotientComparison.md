## What changed

The existing declaration `HomologicalComplex₂.verticalCutoff_cokernel_column_comparison`
keeps its signature and docstring byte for byte. Its proof now explicitly constructs
the natural cutoff-to-window projection, proves its composite with f is zero, and
constructs q using `cokernel.desc`. Each column is transported along the evaluation
cokernel isomorphism; its canonical projection equation is checked in Lean.
The only added proof import is `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIso`
(plain `import`, since its theorem is only used by the proof).
A private natural-transformation construction `windowProjection` contains no sorry
and selects no arbitrary data from an unproved existence theorem.

Removed the first worker's `VerticalCutoffQuotientComparisonAux` and both proposed
nodes. Replaced them by a single-column verification theorem in its own new module.
This theorem specifies the composite of q with the cokernel projection, hence
uniquely identifies the comparison map. It does not assert arbitrary q is a
quasi-isomorphism.

## Proved and sorry left

Closed the original hole in
`HomologicalComplex₂.verticalCutoff_cokernel_column_comparison`.
Added one hole:
`HomologicalComplex₂.verticalCutoff_column_quasiIso`, node
`lem-sp-vertical-cutoff-column-quasiiso`.
There are no other sorries in the delivered files. This is a decomposition: one
upper hole closed, one strictly smaller single-column homology hole added, net zero.
The bicomplex construction, annihilation, cokernel descent, projection equation and
transport of quasi-isomorphisms are proved. The single-column lemma remains open;
its degreewise kernel argument is recorded completely in its docstring and node.
The first worker's two proposed holes, map and quasiIso, are not delivered.

## No longer needed

No repository import or old proof-dependency node is removed: the window definitions
and tower-map definitions are still used. No existing reachable module is claimed
pruned. The undelivered Aux module and its two proposed new nodes were removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's map helper merely asserts existence of a morphism together with
True, so zero proves it without doing any comparison construction. Its quasiIso
helper is false: take abelian groups and a bicomplex concentrated at horizontal and
vertical degree zero with value Z, a=0, b=1. The smaller cutoff is zero and the
window has nonzero degree-zero homology. Taking q=0 is allowed by the helper's
signature but cannot induce an isomorphism on this homology.
The first worker also omitted Mathlib searches and blueprint metadata from its new
nodes, did not update the parent proof record, and left line-length warnings.
These faults are repaired, rather than delivered as a false reduction.

The inherited parent citation to tag 012X concerns spectral sequences; the explicit
canonical truncation formulas are in Stacks tag 0118. The new lemma cites 0118 and
Mathlib's complementary-truncation comparison and labels the nested-cutoff kernel
argument as agent-written. No unit or chapter route was changed.

## New nodes

`lem-sp-vertical-cutoff-column-quasiiso`: verification for one nonnegative cochain
complex and its canonical quotient projection, with no horizontal naturality or
bicomplex construction assertion. Its complete kernel proof includes a=b, b<=0,
a<0 and a=0. Searches through LeanSearch (service unavailable), Loogle and Mathlib
rg found complementary-cutoff APIs, not an exact nested-cutoff result. The upstream
and Sheaf trees also contain no exact single-column theorem with this projection
equation. No change record is needed: no existing signature, definition, visibility
or public import changed.

## Second reading by C2

1. Compared the main module to the repository by diff and the declaration parser:
   the existing theorem signature and docstring are byte-for-byte unchanged; no
   target, existing definition or public import changed. Verdict: pass after repair.
2. Compiled both modules locally with lcompile.py in import order, without errors
   or warnings. A scratch copy with #print axioms reports only propext,
   Classical.choice, Quot.sound and sorryAx for the main theorem and new helper.
   The helper is the one named public theorem whose whole proof is sorry; no
   axiom/unsafe/opaque/implemented_by/extern or sorry in any definition occurs.
   Verdict: valid conditional reduction, not a fully closed proof.
3. Rejected the false arbitrary-map helper using the concentrated-Z example above.
   Verified that the replacement's projection equation determines q uniquely and
   matches the contractible two-term image-kernel argument. Checked empty intervals,
   intervals below zero, a=0, and a<0. Performed fresh searches with different terms
   and inspected the relevant Mathlib and upstream code. Verdict: one true, needed,
   strictly smaller statement remains; not an existential restatement of the item.
4. The proof follows the shortest available route for the bicomplex construction:
   natural truncation projection, complementary-support zero map, cokernel descent,
   evaluation-cokernel isomorphism. No unit realization is bypassed; the attached
   unit's realized record is unchanged. The unchanged public import supplies the
   statements; the new plain import supplies only the remaining proof lemma.
   No old proof dependency becomes unused. Verdict: pass, no existing pruning.
5. Updated the parent node's proof, proof_deps and proof_origin to the explicit
   construction and single-column reduction. The new node has its exact Lean
   signature, source, full proof, search records, creation and blueprint fields,
   chapter, unit and Lean record. Verdict: node records now match the delivered code.

Second reading changed: replaced the false two-hole split by a concrete canonical
comparison construction and one correctly specified single-column homology hole;
removed the invalid Aux module/nodes, repaired source precision and DAG metadata,
and recorded the decomposition honestly.
