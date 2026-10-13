## What changed

Proved the geometric step of the node from Mathlib: section ring, inverse-image open,
compactness and quasi-separatedness, restriction followed by the affine isomorphism,
and cancellation proving the chart square. The certificate is proved by eliminating
this chart and applying derived transport on the fixed square. Two proof-only imports
were added, ProjectionMateAffineChartData and ProjectionMateAffineChartTransport.
The original declaration's signature and visibility are unchanged.

## Proved and sorry left

Closed AlgebraicGeometry.exists_projectionMate_affineChart_certificate.
Proved AlgebraicGeometry.exists_projectionMate_affineChart_data without sorry.
Added one hole, AlgebraicGeometry.projectionMate_affineChart_transport
(lem-pc-projection-mate-affine-chart-transport). This is a decomposition/partial proof:
one upper hole closed, one lower hole added. The lower statement takes a fixed chart
and handles only the coupled derived restriction, isomorphism/localization transport
and cohomology implication, precisely steps 2--3. It is not the geometric existence
statement under another name. No definitions or choices of data from mere existence
proofs are added.

## No longer needed

No original imports or existing modules are globally pruned. The original restriction,
pullback/tensor, direct-image and quasi-coherence dependencies remain needed indirectly
by the lower transport argument, including the existing open-restriction arrow comparison.
They are not direct proof dependencies of the parent. The geometric module uses only
Mathlib quasi-compact and quasi-separated morphisms. Exploratory scheme-isomorphism-only
and private cohomology helpers are not delivered.

## Where the brief, the DAG or earlier work was wrong

The previous ABANDON did not formalize a step of the plan. The geometric step is directly
provable from Mathlib. The existing exists_derivedProjectionMate_openRestriction_comparison
provides the open-localization arrow comparison and is named by the lower node rather
than duplicated as a new open-descent statement. I attempted to assemble it with a
smaller scheme-isomorphism transport lemma and a proved private cohomology helper;
the generic helper compiled, but assembly repeatedly exceeded the single-file limit.
The delivered reduction retains the complete geometric proof and groups the remaining
coupled transport as the allowed intermediate step, using the earlier compiling assembly.
No dependencies or target statements were changed to bypass that difficulty.
Empty opens use the zero section ring and are covered by the construction. The lower
statement fixes all chart geometry and constructs q,s,N,E together: the implication is
not asserted for arbitrary independently selected affine objects. The unit's route is
retained. Stacks 08EU and 08FE were read online; local literature sources are absent here.

## New nodes

lem-pc-projection-mate-affine-chart-data, ProjectionMateAffineChartData: the geometric
square, with no derived-category input, proved by the actual section-ring construction.

lem-pc-projection-mate-affine-chart-transport, ProjectionMateAffineChartTransport:
steps 2--3 on a fixed commuting square, with the full restriction/conjugation/homology
argument in its docstring. It uses the existing open-restriction comparison and canonical
scheme/localization equivalences. Both nodes retain the parent's chapter, unit and
blueprint ancestry. No statement changes or forced adaptations are made.

## Second reading by V4

1. Compared every delivered module with the repository. The target declaration signature is byte-for-byte unchanged; the two additional modules are new nodes and are declared in the report. Verdict: pass.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds. The parent certificate is proved, while the transport theorem is the single named `sorry` listed above. No axioms, unsafe declarations, or hollow definitions were added. Verdict: pass.
3. Checked both split-off statements against their docstrings and DAG nodes. The chart-data theorem is the geometric construction; the transport theorem fixes chart geometry and states only the remaining implication, so it is strictly simpler than the parent and not a restatement. Verdict: pass.
4. Checked the proof route and imports. The parent uses the chart-data and transport declarations; the unit route through affine chart reduction is retained. The transport hole is explicitly documented as the remaining coupled derived step. Verdict: pass.
5. Checked node Lean records, proof steps, dependencies, source, chapter and unit fields against the delivered declarations. Verdict: pass.

Changed only the report by adding this independent second-reading record; no further Lean or DAG changes were needed.
