## What changed

Proved `CategoryTheory.exists_directed_reindexing` in
`Sheaf.CategoryTheory.ExistsDirectedReindexing` directly from Mathlib.
Added proof-only imports `Mathlib.CategoryTheory.Presentable.Directed` and
`Mathlib.CategoryTheory.Limits.Final`; retained the existing public import.
The directed partial order from `IsFiltered.exists_directed` supplies its
underlying preorder. Final and initial whiskering equivalences give the two
clauses for the same functor. No declaration signature or definition changed.
Updated the item's DAG proof, proof dependencies and proof origin to this route.
The existing declaration docstring describes the longer original argument.

## Proved and sorry left

Proved `CategoryTheory.exists_directed_reindexing`
(node `lem-weil-pbc-filtered-category-directed-cofinal`): 1 of 1 original sorries.
No sorry remains in the module, and no new statement or sorry was added.
The proof uses only Mathlib, with no project theorem containing sorry.
Local compilation succeeded; the delivery dry run checks compilation and axioms.

## No longer needed

No existing import was removed: the original module imported only
`Mathlib.CategoryTheory.Filtered.Basic`, which supplies its public signature.
The proof no longer needs nodes
`lem-weil-pbc-initial-functor-cofiltered-criterion` and
`lem-weil-pbc-initial-functor-limit`; neither has a project Lean module recorded
(they are Mathlib leaves). Their explicit cofiltered equalization and zigzag
arguments are replaced by Mathlib's final/initial whiskering equivalences.
Retained `lem-weil-pbc-filtered-category-exists-directed-final`, realized directly
by `CategoryTheory.IsFiltered.exists_directed`.
This pruning is local to this item; other users of those nodes are unaffected.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The original DAG route is unnecessarily long:
Mathlib already packages final-colimit and initial-limit transport, including
initiality of the opposite of a final functor. This node is not a realized unit
statement or unit proof step, and the fixed route of `sk-thm-iff` is preserved.
The empty-index edge case is excluded by `IsFiltered J`; the witness returned by
Mathlib is explicitly nonempty. Singleton categories and directed preorders
require no exceptional treatment. No completeness hypotheses on C were added.
Searches through the provided LeanFinder and Loogle wrappers located
`IsFiltered.exists_directed`; direct Mathlib source inspection located both
whiskering equivalences and `initial_op_of_final`.

## Second reading by P2

1. Compared the delivered module with the repository version. Existing
   declaration signatures and definitions are byte-for-byte unchanged; only
   proof-only imports and the theorem proof differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or
   warnings. A scratch `#print axioms` reports only `propext`,
   `Classical.choice`, and `Quot.sound`; there are no `sorry`s, axioms,
   unsafe declarations, or hollow definitions. Verdict: pass.
3. No statement was split off and no new node was added. The theorem is a
   direct application of Mathlib's directed reindexing and final/initial
   whiskering equivalences, so there is no duplicate project or Mathlib
   statement. Verdict: pass.
4. The proof follows the shortest available route below the unit: obtain the
   directed final functor, then apply the two transport equivalences. The
   unit route and its realized node remain intact. Verdict: pass.
5. The DAG proof, dependencies, and origin match the Lean proof: the sole
   project dependency is `IsFiltered.exists_directed`, while both transport
   steps are Mathlib declarations. Verdict: pass.

Changed only the theorem proof and added the two proof-only Mathlib imports;
no repairs or statement changes were needed.
