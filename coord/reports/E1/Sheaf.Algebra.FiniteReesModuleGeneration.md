## What changed
Added `finite_rees_module_single_degree_generation_of_fg`, an intermediate theorem
whose finite-generation input is the finitely generated top-submodule proposition.
The original theorem is now proved by installing the supplied `Module.Finite` instance
and applying `Module.Finite.fg_top`.

## Proved and sorry left
The original declaration `AlgebraicGeometry.finite_rees_module_single_degree_generation`
is proved. The intermediate declaration
`AlgebraicGeometry.finite_rees_module_single_degree_generation_of_fg` remains `sorry`
(node `lem-weil-pbc-finite-rees-module-single-degree-generation-of-fg`).

## No longer needed
None. The original imports remain needed for the statement and proof.

## Where the brief, the DAG or earlier work was wrong
The original DAG proof plan omitted the finite-generation extraction step. This
 delivery makes that step explicit as a named intermediate theorem.

## New nodes
`lem-weil-pbc-finite-rees-module-single-degree-generation-of-fg` records the new
intermediate theorem and its Stacks Project source.

## Earlier second reading (a previous round; superseded)
The target theorem's signature is unchanged. The new intermediate theorem is a
strictly more explicit decomposition: its input is a finite-generation witness
rather than a typeclass, and the target theorem supplies that witness via
`Module.Finite.fg_top`. The homogeneous-generator argument is documented and
remains the sole open proof obligation.
Change record: `coord/changes/finite-rees-fg-intermediate.md`.

## Second reading by E1

1. **Visible interface.** Compared the delivered module with the repository version. The
existing theorem signature is byte for byte unchanged; the proof is the only declaration
change. The intermediate theorem and its change record were removed because they merely
restated the target argument with a `FG` hypothesis.

2. **Proof and axioms.** Compiled the module with `lcompile.py`; it is clean apart from no
warnings in the final file. A scratch probe reports only `propext`, `Classical.choice`, and
`Quot.sound`. There are no `sorry`, axioms, unsafe declarations, or hollow definitions.

3. **Statements and edge cases.** The target statement is unchanged and the proof handles
`k = 0`, empty supports, zero vectors, `c = 0`, `I = 0`, and `I = A`. The proof uses the
actual finite-generator extraction `Module.Finite.fg_top`, bounded direct-sum supports,
monomial convolution, ideal-power factorization, and span induction. No new statement was
added.

4. **Pruning and route.** The two original Mathlib imports remain necessary for the stated
Rees algebra and direct-sum operations. The proof follows the Lemma 02OA finite graded
Rees-module route. The formerly proposed `of_fg` node and change record were deleted as an
unnecessary restatement; the target node now records the direct proof and has no proof
dependencies.

5. **DAG agreement.** Updated the target node's proof steps and proof origin to match the
implemented bounded-support and span-induction proof. Its Lean signature is copied verbatim
from the module. The unit route remains `sk-thm-p1`.

What changed: replaced the open helper decomposition with a complete proof of
`finite_rees_module_single_degree_generation`; removed the helper node and change record;
updated the target node; and added this review.
