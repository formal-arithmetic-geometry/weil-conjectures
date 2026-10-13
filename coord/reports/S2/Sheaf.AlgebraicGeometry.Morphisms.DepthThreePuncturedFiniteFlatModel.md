## What changed

Replaced the single sorry in
`AlgebraicGeometry.Scheme.exists_finite_flat_model_of_depth_three_of_quotient_extension`
with a compiling reduction to completed lifting and finite completion gluing.
The existing statement and public imports are unchanged. Both new modules are
proof-only imports. The proof transfers etaleness across the gluing comparison,
proves that the completion map is faithfully flat using Mathlib, descends etaleness
using Mathlib's fpqc descent instance, and obtains flatness and the etale principal
quotient by instances. It preserves the actual isomorphism over the punctured base.

Added `Sheaf.AlgebraicGeometry.Morphisms.DepthThreeCompletedQuotientLift` for the
complete-case step of 0BLS, and
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFiniteGluing` for 0BLH.
These statements are independent parts of the argument: the former produces a
model only over the completion; the latter assumes such a completed model and
provides a finite algebra with both prescribed restrictions, without flatness,
etaleness, depth, or a principal quotient hypothesis. No definition chooses data
from an unproved existence theorem. All existential elimination occurs inside
the proof of the original proposition.

Validation: all three modules compile together with lcompile.py. Searched Mathlib
with LeanFinder, Loogle, LeanSearch (unavailable), and grep; searched both library
roots and the DAG for 0BLS, 0BLH and 0BM6. No existing matching gluing or punctured
full-faithfulness theorem was found. Read Stacks 0BLS, 0BLL, 0BLH and 0BM6 directly.

## Proved and sorry left

Closed one upper hole:
`AlgebraicGeometry.Scheme.exists_finite_flat_model_of_depth_three_of_quotient_extension`.
There is no sorry left in the assigned module.

Added two lower holes:
- `AlgebraicGeometry.Scheme.exists_completed_etale_extension_of_depth_three_of_quotient_extension`
  (`lem-sbc-depth-three-completed-quotient-lift`).
- `AlgebraicGeometry.Scheme.exists_finite_model_of_completed_model`
  (`lem-sbc-punctured-completion-finite-gluing`).

This is a decomposition, not a sorry-free proof: one hole closed, two added,
net minus one. The final faithful-flatness and scheme-property descent argument
is proved in Lean using Mathlib; neither new statement repackages the original
statement. Both remaining theorems have source citations and complete proofs in
words in their docstrings and nodes.

## No longer needed

No existing import or module is pruned. All three original public imports remain
needed by the original statement. The original node's direct proof dependencies
`def-weil-pbc-depth`, `def-weil-pbc-scheme-conventions`, and
`def-weil-pbc-henselian-terminology` move below the new intermediate statements;
they remain necessary there and are not globally pruned. Completion, flatness,
and etaleness remain immediate proof dependencies. The new gluing module needs
no etale import, nor a depth or henselian assumption.

## Where the brief, the DAG or earlier work was wrong

The DAG's original proof steps named definitions but supplied no Lean statements
for completion lifting or finite algebra gluing. Those definitions alone cannot
prove the steps; the two new nodes make the missing mathematical inputs explicit.
The direct Mathlib fpqc descent of etaleness proves the required properties
without separately descending flatness and quotient etaleness.

An initial scratch split separating existence of an unspecified finite flat model
from identification of that model with q was rejected during author checking:
the latter statement would be false for an arbitrary model. Neither scratch
statement is delivered. The final gluing statement retains both comparison maps.
Edge cases checked: f=0 is allowed (its quotient is A); empty covers use the zero
finite algebra; gluing does not require q or the completed model to be etale.
No target statement or existing definition changed. The unit route is retained.

## New nodes

`lem-sbc-depth-three-completed-quotient-lift` states the completed finite etale
extension and its punctured comparison, following the complete-case paragraph
of 0BLS, with 0AVY, 0A02, 09ZL and 0BM6. This is strictly the completed lifting
part, not descent to A.

`lem-sbc-punctured-completion-finite-gluing` states the generic finite gluing result
0BLH, including both comparison isomorphisms and their equations over the base.
It applies to arbitrary finite completed models, with no depth or etale assumptions.
Its proof follows finite module gluing, transfer of multiplication and unit by
full faithfulness, and the Spec construction. The searches are recorded in both
nodes and in searches.jsonl. No change record or forced adaptation is needed.

## Second reading by S2

1. **Visible changes.** Compared the delivered target module with the repository version. The theorem signature and all existing declarations are unchanged byte for byte; only the proof body and proof-only imports were added. The two additional modules are new split-off declarations recorded in the DAG.
2. **Proof validity.** Compiled all three modules with `lcompile.py --all`. The target has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining `sorry`s are the two named split-off theorems, each with a source, proof description, and node.
3. **Statements and nodes.** Checked both split-off statements against their docstrings, source tags, and DAG records. They are strictly smaller than the target: one is completion lifting and the other is finite gluing, and neither restates the target or changes an existing definition.
4. **Pruning and route.** Searched the imported library and Mathlib for existing completion-lifting or punctured finite-gluing results. No matching declaration was found. The original unit route through completion lifting, finite gluing, and descent is retained; no existing import or dependency can be removed.
5. **Edge cases and interfaces.** Checked the statements for the zero/empty-cover and `f = 0` cases described by the source argument, and verified that the gluing theorem imposes no accidental flatness or etaleness assumptions. The target’s conclusion remains exactly the planned finite-flat model with etale principal quotient.

I changed only this report section after the initial worker delivery; no Lean proof or statement required repair.
