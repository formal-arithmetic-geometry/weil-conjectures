## What changed

Replaced the proof of `CategoryTheory.homTensorDegreewiseMap_comm`, preserving its
signature, visibility, docstring, and existing public import byte for byte.
For consecutive degrees the proof uses the specified product projections, expands
the target Hom differential, distributes composition over subtraction and the
integer-unit scalar, and applies a component calculation for the iterated Hom side.
For nonconsecutive degrees it proves both differentials zero using complex shape.

Added `Sheaf.Algebra.Homology.HomTensorDifferentialComponent`, imported privately.
Also privately imported the existing `HomComplexProjections` module to expose the
product-limit and differential specifications without expensive unfolding.
The byte-identical sandbox copy of `HomTensorDegreewise` is only compilation support;
it adds no library change or new hole.

## Proved and sorry left

Hole closed: `CategoryTheory.homTensorDegreewiseMap_comm`
(node `lem-sc-hom-tensor-differential`), by reduction to the component calculation.
Hole added: `CategoryTheory.homTensorDegreewiseMap_iteratedDifferential_component`
(node `lem-sc-hom-tensor-iterated-differential-component`), the explicit formula for
one factor of the curried iterated differential, in the new component module.
There is no `sorry` in the item's module and exactly one in the new module.
This is a decomposition: one original hole closed, one lower hole added, net zero.
The existing `CategoryTheory.homTensorDegreewise_exists` hole in the unchanged
compilation-support dependency is neither closed nor newly added.

## No longer needed

No baseline import or module is pruned. The old direct proof dependencies
`def-pur-hom-complex`, `def-pc-tensor-complex-sheaves`, and
`lem-pc-sheaf-modules-tensor-closed` are replaced on the main node by
`lem-sc-hom-complex-projections` and the new component node, but all three remain
needed transitively in the component calculation. They are not claimed pruned.
The proposed, unpublished `HomTensorDifferentialSucc` module and
`lem-sc-hom-tensor-differential-succ` node were removed from this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier submission moved the entire consecutive-degree compatibility equation
to a new sorry theorem. The second reading replaces that near-restatement with an
explicit one-factor calculation of only the iterated-Hom side; the target-side
expansion and product joint monicity are now actual Lean proof steps.
The initial report called the upper result proved without reporting that the net
hole count was zero. The revised report labels this as decomposition.
The absent compiled degreewise dependency is handled by compiling its unchanged
sandbox source, as the first worker did.

## New nodes

`lem-sc-hom-tensor-iterated-differential-component` states the postcomposition-minus-
signed-precomposition formula for one factor of the iterated differential after
currying. Its module is `HomTensorDifferentialComponent`. Its docstring supplies
the localized pure-tensor calculation and the tensor, sheafification, and coproduct
arguments. No existing interface, definition, or target statement changes;
no change record or forced adaptation is needed.

## Second reading by S3

1. Compared every existing sandbox module with the repository by diff and checked
   signatures with `stage3_delivery.diff_module`: no existing signature changed.
   `HomTensorDegreewise` is byte-identical. Only the main proof and private imports
   change. The new component statement has its own new module and node. Pass.
2. Compiled the unchanged dependency, original submission, and revised modules
   through `lcompile.py`; checked for forbidden declarations and hollow definitions.
   The main proof has no sorry; the new component theorem is the sole added sorry.
   Explicit axiom probes show only propext, Classical.choice, Quot.sound, and sorryAx
   from the open component and preexisting degreewise theorem. No data construction
   is added; the existing degreewise choice is fixed by an existence-and-uniqueness
   theorem, not arbitrary existence. Pass as a decomposition, not a completed proof.
3. Read Stacks Tag 0A90 and the referenced component sign calculation in Tag 0A5Y:
   https://stacks.math.columbia.edu/tag/0A90 and
   https://stacks.math.columbia.edu/tag/0A5Y . The new statement has unrestricted
   complexes and integer degrees, and its two terms have the correct t and t+1
   projections and target degrees. Checked zero complexes, zero differentials,
   n=0, n=-1, and odd/even source degrees; the sign identity is valid in all cases,
   including characteristic two. Its complete proof docstring and node agree.
   Searched Mathlib with new LeanFinder, Loogle, and grep queries, and searched
   lean/Sheaf, upstream InternalHom, and relevant DAG nodes. Upstream
   `curryCochain_δ` and `uncurryCochain_δ` use a different categorical Hom-complex
   construction and signed curry convention, so do not directly prove the formula
   for these chosen sheaf Hom projections. No duplicate found. LeanSearch also ran
   but returned an Internal Server Error, recorded in searches.jsonl. Pass.
4. Read from the target downward. The final proof uses the existing Hom projection
   specification and elementary shape before leaving the one-factor calculation
   open. Both added private imports are used, and the original public degreewise
   import is needed by the unchanged statement. Every old proof dependency is
   accounted for above. The unit `sk-thm-picard-duality` realized fields and route
   are unchanged; this is below its unit level. Pass.
5. Checked both node files against the final Lean. The main node names product
   joint monicity, differential expansion, and shape, with the two actual proof
   dependencies. The new node records the component formula, full construction
   dependencies, source, searches, blueprint ancestry, creation, and verbatim Lean
   signature. No existing node field outside stage-3 ownership changes. Pass.

Second reading changed: replaced the whole consecutive-degree hole with an explicit
iterated-differential component formula; proved the target-side expansion and
product-extensionality reduction; corrected dependency records and progress report.
