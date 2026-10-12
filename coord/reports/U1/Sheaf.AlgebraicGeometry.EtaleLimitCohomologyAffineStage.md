## What changed

Replaced the sorry of `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_stage`
with a complete proof that the canonical group-colimit comparison is bijective.
Class descent proves surjectivity. The new single-affine-stage eventual-zero theorem
proves injectivity. The proof transports the canonical colimit along this isomorphism,
checking its legs. All existing signatures and visibility remain unchanged.
Added proof imports of EtaleLimitCohomologyClassDescent,
EtaleLimitAffineStageEventualZero and Mathlib.Algebra.Category.Grp.FilteredColimits.
No forced adaptations. Both delivered modules compile cleanly with lcompile.py.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.etale_limit_cohomology_affine_stage` (one of one
original holes). Added: `AlgebraicGeometry.Etale.etale_limit_affine_stage_eventual_zero`
(node `lem-weil-pbc-etale-limit-affine-stage-eventual-zero`), the sole delivered sorry.
This is a decomposition: one upper hole closed and one strictly smaller kernel-detection
hole added, net zero. The imported class-descent theorem is already proved in its module,
but retains the dependencies recorded there; no transitive axiom-freedom is claimed.
The new lemma supplies neither arbitrary class representatives nor a colimit structure.

## No longer needed

The parent now uses elementwise assembly rather than the full cofinal-tail universal
property directly. Its direct proof dependency
`lem-weil-pbc-colimit-initial-full-subcategory` is moved to the new eventual-zero node,
so it is still needed transitively, not globally pruned.
The experimental EtaleLimitCohomologyReindexLegs module and imports
Mathlib.CategoryTheory.Filtered.Final and Mathlib.CategoryTheory.Limits.Final are absent
from the delivery. They were only in the earlier sandbox attempt, not baseline imports.
No existing library module is certified globally unreachable. Pruned: none.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The stale earlier report described a core theorem that simply restated the assigned
statement. That is not an acceptable reduction and is not delivered.
The earlier tail proof caused kernel timeouts while identifying reindexed inverse-image
and cohomology data. A general reindexing helper was proved and compiled experimentally,
but the combined direct proof still exceeded the 60-second limit. Rather than deliver
that uncompilable proof or a renamed copy of continuity, this delivery isolates only
finite-stage zero detection and writes the full bijectivity-to-colimit argument.
The original affine-continuity hypothesis is preserved but unused: the smaller
zero-detection statement will use the existing affine-comparison theorem directly.
No statement is disputed or weakened. Edge cases: zero classes use identity maps;
empty schemes and zero sheaves have zero groups; degree zero uses the same filtered
colimit equality argument; singleton indices reduce to injectivity of comparison.

## New nodes

`lem-weil-pbc-etale-limit-affine-stage-eventual-zero` records the kernel-detection
part for a system with one specified affine stage, in its own Lean module. Its proof
uses affine continuity on the final directed tail and the filtered-colimit equality
criterion. The statement is strictly a part of continuity, with no class-descent or
colimit-universal-property conclusion. LeanSearch (unavailable), Loogle/LeanFinder and grep searches are recorded from
searches.jsonl. The source statements were checked at
https://stacks.math.columbia.edu/tag/09YQ and https://stacks.math.columbia.edu/tag/04AX.

## Second reading by U1

1. PASS: compared both delivered modules with the repository. The existing theorem's
   signature, including its original affine-continuity hypothesis, is byte-for-byte
   identical. Its visibility and sole public import are unchanged. The other module
   is new; no definition or existing interface changes, and no change record is needed.
2. PASS: both modules compiled through lcompile.py (5.7 and 7.1 seconds). Scratch-copy
   #print axioms checks for both declarations returned only propext, Classical.choice,
   Quot.sound and sorryAx. The sole local sorry is the named eventual-zero theorem;
   the upper proof also retains imported open dependencies. No forbidden commands,
   definitions with sorry, or data selected from an unproved existence theorem occur.
3. PASS: the added theorem asserts kernel detection only. Surjectivity is supplied
   independently by the existing class-descent theorem; the parent writes the actual
   injectivity, surjectivity and transport-of-colimit proof. Verified the geometric
   assertion against [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ) and the
   eventual equality criterion against [Stacks 04AX](https://stacks.math.columbia.edu/tag/04AX).
   Checked zero classes (identity transition), degree zero, empty affine schemes,
   zero sheaves, singleton indices, and indices preceding or incomparable with i0
   (move first to a common upper bound). New LeanFinder and Loogle queries and local
   library searches found no exact replacement. The existing affine eventual-zero
   theorem requires every stage affine, so the remaining cofinal-tail coherence
   work cannot be closed by applying it directly in a few minutes.
4. PASS: the parent uses Mathlib's concrete filtered-colimit representatives and
   existing class descent, then only the new strictly smaller kernel statement.
   Its three private imports serve the proof, and its public import serves the
   statement. The new module's public import supplies types used in its signature.
   The old direct dependency lem-weil-pbc-colimit-initial-full-subcategory is listed
   under No longer needed and retained in the new lemma's plan. No baseline import
   was removed. Checked dag/units/sk-thm-p1.json realized: neither edited node
   realizes a unit statement or step; the projective-line route is preserved.
5. PASS after documentation repairs: the parent node records affineness, class
   descent, kernel detection and the filtered-group-colimit assembly, with exactly
   their proof dependencies. The new node has its source, full proof, searches,
   creation and blueprint records and verbatim Lean signature. The dependencies
   on affine comparison and cofinality do not point back to the assigned module.

Second reading changed the parent's stale cofinal-tail docstring to describe its
actual elementwise proof, restored an extra signature whitespace byte, clarified
how the new lemma handles an index outside the affine tail in its docstring and
node proof, added independent search records, and marked the Mathlib-based assembly
step non-elementary. No proof term, hypothesis or conclusion was changed. One
original hole is closed and one smaller hole added: decomposition, net zero.
