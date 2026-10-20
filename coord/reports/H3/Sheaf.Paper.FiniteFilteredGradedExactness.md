## What changed

Proved all five holes in Sheaf.Paper.FiniteFilteredGradedExactness, with existing public signatures and definitions unchanged. Added proved private helpers for exactness of an extension of short complexes, the two finite inductions, quotient-layer exactness and strictness. Updated the existing node to match the direct diagram-chase implementation of the source proof.

## Proved and sorry left

Closed 5 original holes:

- CategoryTheory.FilteredObject.quotientMap_condition
- CategoryTheory.FilteredObject.quotientMap_comp
- CategoryTheory.FilteredObject.restrictionSteps_comp
- CategoryTheory.FilteredObject.gradedMapSteps_comp
- CategoryTheory.FilteredObject.finite_filtered_graded_exactness

Holes added: 0. Sorry left: none. This is a proof, not a decomposition.
Remote compilation succeeds. Explicit #print axioms for all five declarations reports only propext, Classical.choice and Quot.sound. No target signatures or definitions changed.

## No longer needed

Removed the proof imports Mathlib.Algebra.Homology.HomologySequence and WeilConjectures.CategoryTheory.Abelian.Filtration (the latter remains available through the unchanged public filtration imports). Removed the obsolete top-level tool_uses approval for lem-weil-pbc-complex-ses-homology-long-exact. That node is not needed by this proof: its extension-exactness consequence is proved directly using Mathlib.CategoryTheory.Abelian.Refinements. No project module is withdrawn. The exploratory CommSq import was removed too.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The planned finite inductions are valid. The full long exact homology sequence is unnecessary: exact_extension carries out its relevant vanishing argument directly with epimorphic refinements. In fact the hypotheses on Z's finite filtration are redundant in this proof, but the public statement is preserved. No new nodes, definition repairs, or forced adaptations.

The retained packet was checked against current sources on 2026-10-20. The required deliver3.py --no-push completed successfully: compilation and preflight pass. The previous attempt’s delivery-tool stall did not recur. Independent review is required for the node update and the private instances.

## Second reading by H3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
