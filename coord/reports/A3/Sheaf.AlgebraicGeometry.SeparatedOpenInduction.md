## What changed

Proved `AlgebraicGeometry.separated_quasiCompact_open_induction` directly using
Mathlib's `compact_open_induction_on`. The invariant carries both `P U` and
`P (U ⊓ T)` for all affine `T` contained in the fixed separated open `W`.
A local proved helper transports affine intersections through `W.ι`.
No existing declaration signature or definition changed. Restored the original
module and theorem documentation omitted by the first worker.

Removed the unproved `SeparatedOpenInductionCore` module and its proposed node;
the finite-cover reformulation had merely moved the essential argument.
Removed two redundant direct imports; `Morphisms.Separated` publicly imports
their declarations transitively and is required by the statement.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.separated_quasiCompact_open_induction` (node
`lem-sc-invert-s-cohomology-separated-induction`). Added zero holes; no `sorry`
remains in the delivered module. This is a proof, not a decomposition.
The proposed hole `AlgebraicGeometry.separated_quasiCompact_open_induction_core`
is removed along with its undelivered module and node.

## No longer needed

Removed direct imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` and
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` as redundant through the
remaining public import `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
They remain transitive dependencies, so no library module is claimed pruned.

Removed old proof dependencies `lem-weil-pbc-separated-cancellation` and
`lem-weil-pbc-proper-fp-permanence`: the strengthened invariant avoids proving
separatedness of intermediate unions. Retained the finite-affine-cover and
affine-intersection nodes, whose Mathlib realizations the proof uses.
The proposed `Sheaf.AlgebraicGeometry.SeparatedOpenInductionCore` import and
node `lem-sc-invert-s-cohomology-separated-induction-core` are also removed.

## Where the brief, the DAG or earlier work was wrong

The first worker's core was not a strict smaller remaining problem: compactness
and a finite affine cover are interchangeable here, so its unproved theorem
carried essentially the whole item. Its docstring also omitted the overlap
induction argument, and the original node was not updated to reflect its use.
The existing DAG route can instead be implemented with a strengthened invariant
and existing Mathlib facts. No mathematical error in the unit route was found.

## Second reading by A3

1. Compared the complete delivered module with the repository using `diff` and
   asserted equality of the full theorem signature through `:= by`, byte for
   byte. The qcqs hypotheses, affine premise, five gluing premises, separated
   compact open W, and conclusion P W are unchanged. No definition is changed.
   Verdict: pass after replacing the proposed core reduction.

2. Compiled the final module locally through the prescribed `lcompile.py`.
   A scratch copy containing `#print axioms` compiled without warnings and
   reported exactly `propext`, `Classical.choice`, `Quot.sound` for the target.
   Searched every delivered Lean source for sorry and forbidden declarations;
   none remain. Verdict: complete proof with no new assumptions.

3. Read the proposed core and its node: they restated the same induction with
   an explicit finite-cover witness. Removed both instead of accepting the
   decomposition. LeanFinder with an alternative induction query found
   `compact_open_induction_on`; grep confirmed its proof and `IsAffineOpen.inf`.
   Searched project Lean sources for existing induction and intersection lemmas.
   There are now no split-off statements or new declarations to review.
   The empty-cover case uses `isAffineOpen_bot`; one chart uses the affine
   premise, and two charts use their affine intersection inside W. Verdict: pass.

4. Read Stacks 08DR, proof first paragraph, at
   https://stacks.math.columbia.edu/tag/08DR (the source tex is absent locally).
   The proof retains finite-affine-cover induction and affine overlaps. In the
   step, containment of U union V in W supplies both containment premises for
   the intersection helper; quasi-separatedness of X supplies compactness of
   U intersect T. The inductive hypothesis at V intersect T supplies the triple
   overlap, so neither gluing application assumes its conclusion.
   Removed redundant imports and listed both unused old proof dependencies
   above. `dag/units/sk-thm-curveestimate.json` realizes its statement by
   `thm-sc-proper-cohomology`, with no step realized by this node; its realization
   and the chapter/unit routes are unchanged. Verdict: pass.

5. Updated the original node's `proof`, `proof_deps`, and `proof_origin` to
   describe precisely the affine-intersection helper and strengthened compact
   induction. The retained dependencies are Mathlib leaves: the cover criterion
   used by `compact_open_induction_on`, and the affine-intersection criterion
   used by `IsAffineOpen.inf`. No new node is needed. The redundant public-import removal is recorded in
   `coord/changes/SeparatedOpenInductionImports.md`; all transitive downstream
   users retain the same public declarations.
   Verdict: pass.

Second reading changed the proof to a complete Mathlib-based induction, removed
the unproved core and its node, restored documentation, removed redundant
imports, corrected the DAG proof route, and replaced the inaccurate report.

## Change records

`coord/changes/SeparatedOpenInductionImports.md` documents redundant public-import
removal and its effect on every transitive downstream module. The dry-run
preflight requested this record; no statement or definition changed.
