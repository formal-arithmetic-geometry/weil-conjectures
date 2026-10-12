## What changed

The unchanged theorem `CategoryTheory.Functor.secondFiltration_signed_firstPage`
now has a complete Lean proof from the normalized row-cycle quotient comparison.
Its signature and its public imports are unchanged. The new proof-only import is
`Sheaf.CategoryTheory.SecondFiltrationRowCycleComparison`.

The private, fully proved `row_cycle_total_d` expands the total differential on a
row-cycle diagonal inclusion. It proves that the resolution component vanishes
and the remaining component is the signed row chain map, using Mathlib's
`total_d`, `ι_D₁`, `ι_D₂`, `d₁_eq`, `d₂_eq`, `extend_d_eq`, `extendMap_f`,
`iCycles_d`, and `cyclesMap_i`. The main theorem then applies
`D.on_representatives` to these actual lifts, uses `homologyπ_naturality`, and
cancels the epic cycle-to-page projection. None of this differential calculation
is postponed to a new theorem.

The new module constructs `secondFiltrationRowι` explicitly from the inverse
extension isomorphism and the total coprojection. It states the remaining
normalized quotient comparison. Its theorem has no D argument and no conclusion
about a page differential, signed or otherwise. The object comparisons are fixed
by explicit lift and quotient equations; no arbitrary witness from an unproved
existence theorem is used to define data.

Both modules compile together through the launcher. The existing node's proof,
proof dependencies, and proof origin now describe the Lean reduction. The unit
record has empty realized lists and no unit step is bypassed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.Functor.secondFiltration_signed_firstPage`
(node `lem-sp-second-filtration-signed-first-page`). There is no sorry in the
item module. The new private `row_cycle_total_d` and the concrete public
`secondFiltrationRowι` also have complete proofs/constructions.

Added one hole:
`CategoryTheory.Functor.secondFiltration_row_cycle_comparison`
(node `lem-sp-second-filtration-row-cycle-comparison`) in
`Sheaf.CategoryTheory.SecondFiltrationRowCycleComparison`.
It is exactly `:= by sorry`, with its source, detailed proof, and blueprint tag.

This is a decomposition: one original hole closed, one strictly smaller hole
added, net zero holes. The quotient comparison remains open; the signed
representative calculation and its descent to the page differential are proved.
The remaining statement was checked at r=0 (zero incoming extended term), at
negative s (the relevant interval is [s,s+r]), and for zero rows (unique maps
between zero objects). No target or intermediate statement was changed.

## No longer needed

The item's direct proof import
`Sheaf.Algebra.Homology.FilteredComplexFirstPageCyclesBoundaries` was replaced
by the normalized comparison module. That cycles/boundaries theorem remains
needed for the new comparison node and its module imports it; it is not pruned
from the target closure. Its direct dependency, together with
`def-sp-filtration` and `def-sp-filtered-complex-subquotients`, now belongs under
the new comparison node instead of the signed calculation.

No module or mathematical node is pruned from the target closure. The retained
public imports `CartanEilenbergPresentation` and `FilteredComplexPageDifferential`
are needed by the unchanged statement. No higher-page or spectral-sequence
construction was added to the proof.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or forced adaptation. The existing
`HomologicalComplex₂.secondFiltration_graded` has a first-quadrant hypothesis
in both integer coordinates; it cannot directly supply the comparison here,
where the complex coordinate has only an arbitrary lower bound. The new
comparison proof explicitly uses the finite tail [s,s+r], including negative s,
so it does not silently strengthen hbelow to a first-quadrant assumption.

The local `literature/stacks-project/homology.tex` file was absent on this
machine. The source formulas were read at
https://stacks.math.columbia.edu/tag/0130 (clauses 2 and 4, proof omitted) and
https://stacks.math.columbia.edu/tag/012K (cycle/boundary quotients and the
representative differential). LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as a negative search result. Loogle,
LeanFinder, Mathlib grep, and library grep found general tools but no matching
normalized comparison. The blueprint search returned only the existing total
complex definition, not a duplicate of the new statement.

## New nodes

`lem-sp-second-filtration-row-cycle-comparison`, in
`dag/nodes/sec-abelian-varieties/lem-sp-second-filtration-row-cycle-comparison.json`,
states the normalized filtration lift, graded-cycle lift, and quotient
comparison, without mentioning a page differential. It records the remaining
object/kernel/image/cokernel construction from steps 1 and 2 of the original
plan, with a complete proof in words, source, actual searches, and Lean
signature. The new module is
`lean/Sheaf/CategoryTheory/SecondFiltrationRowCycleComparison.lean`.
There are no interface change records and no adapted modules.


## Second reading by M3

1. PASS — Compared the complete item module and existing node with the repository
   versions. The existing theorem signature is byte-for-byte identical, including
   every hypothesis and conclusion; its docstring and public imports are unchanged.
   The existing node differs only in proof, proof_deps, and proof_origin. The other
   module and node are new. There are no interface changes or change records.

2. PASS — Compiled both modules in import order with lcompile.py (1.9 and 2.9
   seconds). Scratch copies with #print axioms show that secondFiltrationRowι and
   row_cycle_total_d use only propext, Classical.choice, and Quot.sound. The main
   theorem and comparison additionally use sorryAx, as expected from the one named
   open comparison. The only delivered sorry is that comparison's exact `by sorry`
   body; there are no forbidden declarations or hollow definitions. Read the total
   differential expansion and the representative descent through epi cancellation.
   Each step proves the equation it claims, including the sign from the resolution
   index and the homology-map naturality equation.

3. PASS — The new comparison is a strictly smaller object/cycle/quotient comparison,
   with no D parameter and no page-differential conclusion. Its three equations
   normalize the actual diagonal lifts and quotient map; no data is defined by
   arbitrary existence. Read its full docstring proof and DAG proof against Stacks
   https://stacks.math.columbia.edu/tag/0130 and
   https://stacks.math.columbia.edu/tag/012K. Checked degree zero (incoming extended
   term vanishes), a row supported in one degree (cycles modulo its actual incoming
   image), negative s (finite tail [s,s+r]), and zero rows. These give the claimed
   normalizations and homology objects, with no extra vanishing hypothesis needed.
   Independent searches used Loogle `HomologicalComplex.extendXIso`, LeanFinder
   `homology of associated graded complex for the column filtration of a bounded
   below bicomplex`, Mathlib grep `gradedPiece.*homology|extendCyclesIso`, and local
   rg on graded homology, row cycles, and secondFiltration. They found extension
   cycle comparisons and general graded homology tools, not this normalized result.
   The existing secondFiltration_graded requires vanishing in both negative
   coordinates, which does not follow from an arbitrary integer lower bound here.
   Closing the remaining comparison needs its graded and quotient constructions;
   it is not a few-minute application of a matching theorem.

4. PASS — The proved differential calculation opens the original hole and uses
   Mathlib's total, extension, cycle-map, and homology-map lemmas directly. The
   remaining comparison isolates only the original plan's object identification.
   The item's removed proof imports are FilteredComplexFirstPageCyclesBoundaries,
   FilteredComplexSubquotients, DoubleComplexTotal, and Filtration; their required
   material remains transitively available through the comparison module, and the
   first two former proof dependencies move under the new node along with Filtration.
   No module leaves the target closure. Public imports support the statements;
   the new comparison and its cycles/boundaries proof dependency are plain imports.
   Read dag/units/sk-prop-av-pqf-finite.json: its realized statement and step lists
   are empty and remain unchanged; no realized unit node is bypassed. This is one
   hole closed and one hole added, a decomposition with net zero holes.

5. PASS — Checked both DAG proof step lists and their proof_deps unions against
   the Lean reduction and the remaining comparison proof. The existing node's
   origin accurately separates the completed signed calculation from the open
   quotient identification. The new node has its source, searches, provenance,
   blueprint, chapter, unit, status, and verbatim Lean theorem signature, with both
   public declarations recorded. Its stated proof contains the finite diagonal
   lift, graded differential, kernel/image comparison, and cokernel normalization
   needed by the theorem.

Second reading changed only this report: added the independent checks and made
explicit all four removed direct proof imports. No Lean or DAG repair was needed.
