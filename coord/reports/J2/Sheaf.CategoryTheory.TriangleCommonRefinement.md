## What changed

Proved `CategoryTheory.triangle_common_refinement_and_equalization` in
`Sheaf.CategoryTheory.TriangleCommonRefinement`, with its original signature and visibility.
Added only the proof import `Mathlib.Data.Fintype.Option` for finite-type induction.
The existing public import and denominator-completion proof import remain.

Private, proved helpers implement closure under composition, saturation cancellation,
componentwise equalization, correction of the three triangle squares, binary refinement,
and finite-family induction. All constructions are used inside proposition proofs;
no definition chooses data from an unproved existence statement.

The proof follows the existing node's route and proof dependencies, unchanged. For binary
refinement, three right-fraction squares give component maps over the target. Saturation
puts their numerators in S. Three further right-cancellation steps and denominator
completions impose the triangle squares; the third uses shift compatibility. Empty families
use the identity of the given distinguished triangle. Option induction adds one triangle
at a time. Parallel maps are equalized in the first, second, and third components, preserving
previous equalities by precomposition.

Validation: local single-file compilation succeeds without warnings. Search used leanfinder,
loogle, and grep through msearch.py, plus source searches. No shorter matching theorem was
found. The source was checked at https://stacks.math.columbia.edu/tag/05R9, with arrows reversed.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.triangle_common_refinement_and_equalization`
(node `lem-pur-triangle-common-refinement-ms3-05r9`).
No sorry remains in the item, and no new hole, node, or module is added.
This is a proof from the stated dependencies, not a decomposition into new holes.
The proof still depends on the existing
`CategoryTheory.denominator_triangle_completion`
(node `lem-pur-triangle-completion-ms6-05r9`, module
`Sheaf.CategoryTheory.Triangulated.DenominatorTriangleCompletion`), whose sorry is outside
this delivery. Consequently the delivered theorem is not yet axiom-clean independently
of that existing dependency.

## No longer needed

None. No existing import, node, or module was removed: both stated proof dependencies
are used. No unit route is bypassed (`sk-def-sf-operations` has no realized statement or steps
at this node). No additional planned theory was imported.

## Where the brief, the DAG or earlier work was wrong

The checkout does not contain `literature/stacks-project/derived.tex`; the published
Stacks Tag 05R9 supplies the source. The proof plan itself fits the Lean interfaces.
No statement or definition was changed, and no forced adaptation was needed.

## Second reading by J2

1. Compared the complete delivered module against the repository version. The sole existing
   theorem's signature is byte-for-byte identical, and its docstring, visibility and public
   import are unchanged. Only private proved helpers, a proof-only Option import and the
   replacement proof were added. No statement change or forced adaptation: pass.
2. Recompiled the module locally: exit 0 in 1.8 seconds, no warnings. Searched for prohibited
   declarations and holes: none. Compiled a scratch copy with
   `#print axioms CategoryTheory.triangle_common_refinement_and_equalization`: exactly
   `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`. The latter comes from the existing
   `denominator_triangle_completion`, not a new hole. `Denom` is an explicit conjunction;
   all existential witnesses are eliminated within proposition proofs, without exporting
   arbitrary data chosen from an unproved existence statement: pass.
3. No statements or holes were split off. Read each private helper. `mem_of_comp` uses a
   right-fraction square and cancellation to make a left composite lie in S, then applies
   MS4 with the known right composite. `rectify` precomposes successively at vertices one,
   two and three; its third square correctly uses `S.shift` on the target's first component.
   Earlier squares survive each precomposition. The binary construction obtains the
   component numerators' membership using saturation before invoking `rectify`. Pass.
4. Read the dual construction in published Stacks Tag 05R9 and the existing completion
   interface. Empty families use T and its identity; Option induction adds one member by
   binary refinement, so no nonemptiness restriction slipped in. Equalization only needs
   the source distinguished and the target denominator, correctly retaining all original
   hypotheses in the public theorem. Repeated searches with leanfinder (right fraction
   calculus on distinguished triangle morphisms), loogle (fully qualified RightFraction),
   grep (Triangle/IsCofiltered), and rg in both library roots and Mathlib found no shorter
   matching result. Existing TriangleMorphismCategory uses this item and cannot replace it.
   All three imports are used; the Option import and completion import are proof-only.
   Both old proof_deps remain necessary, so the pruning list is complete. The unit's
   `realized` has no statement or steps at this node; no unit route is bypassed: pass.
5. Compared the node's proof, proof_deps and proof_origin with the proof as written. The
   three component square completions, three triangle-square corrections, finite induction
   and successive equalizations implement the recorded route. Corrected a pre-existing
   notation error in proof step 2: the parallel arrows agree after composition with the
   denominator T_2 → T, not s_1 (whose domain is T_1). Updated proof_origin to record the
   published source check. No dependency, statement or Lean record changed; no new nodes.
   Verdict: pass after this narrative correction.

Second reading changed only the existing node's proof narrative/source-check record and
this report. The Lean proof required no repair. Closed one original hole, added zero holes;
no module or dependency was pruned. Dry run and delivery use deliver3.py as instructed.
