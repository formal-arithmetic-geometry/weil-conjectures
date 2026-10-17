## What changed

Repair of the stale-base return at head `b8b490ffc`: read the current shared module,
reapplied the finite-level quotient proof and completion proof to that file, and
preserved its current public imports and exact public theorem signature. The current
shared module still has one theorem hole and its old helper disabled; this delivery
replaces that hole with the complete argument, rather than submitting a rebase alone.
Rebuilt the sandbox node from the current shared node, carrying forward only the
proof, proof dependencies and proof origin owned by this delivery.

Proved `AlgebraicGeometry.formalCompletion_affine_sections` in
`Sheaf.AlgebraicGeometry.FormalCompletionAffineSections` with its statement unchanged.
Restored and proved the private finite-level helper `quotient_sections_iso` using only
public declarations. The affine tensor comparison computes the ideal-product range;
affine cokernel exactness supplies the surjective projection and its kernel. The first
isomorphism theorem gives the quotient isomorphisms. Their projection equations prove
transition compatibility, and `adicCompletion_iso_of_stable_ranges` with shift zero,
followed by the limit-preservation isomorphism for evaluation, gives the completion
isomorphism with the required projections.

Changed the ideal-times proof import from `import all` to an ordinary `import`, and
added a proof-only import of
`Sheaf.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections`. All existing public
imports, declarations, statement signatures, and definitions remain unchanged. Updated
the item's DAG proof and dependencies to record the public tensor/image calculation.
No other module is adapted and no change record is needed for this proof-only repair.

## Proved and sorry left

Closed: `AlgebraicGeometry.formalCompletion_affine_sections`
(node `lem-weil-pbc-formal-completion-affine-sections`): 1 of 1 original holes.
The restored private helper `quotient_sections_iso` is fully proved.
Added: 0 holes. Remaining in this delivery: 0 holes. No decomposition or split-offs.

The retained proof recompiles against the current published build without warnings
using `lcompile.py` (18.3 seconds). The prior independent reading and axiom probe
reported exactly `propext`, `Classical.choice`, and `Quot.sound`. Its argument covers
the zero ideal, unit ideal, zero module and empty affine open without nontriviality,
Noetherian or finite-generation hypotheses. Quotient isomorphisms are determined by
their equations on surjective quotient projections; no arbitrary object is selected
from a merely existential unproved statement.

## No longer needed

No mathematical node or module is pruned: every original proof dependency remains
used. The `all` visibility import of the ideal-times module and its private
`Scheme.Modules.product_qc` and `Scheme.Modules.multiplication_range` helpers are no
longer needed. The corresponding facts are calculated inside the proved finite-level
helper from the public tensor, ideal-power and cokernel-image statements. No public
imports are removed.

## Where the brief, the DAG or earlier work was wrong

The landing return concerns a concurrent write after base `3a59fd77e`, not a rejected
mathematical argument. Compared the retained delivery with the current shared module
and rebuilt the proof on the current version. The current interface is identical to
the retained proof's interface; no consumer or definition adaptation is required.
The dry run below constructs a fresh delivery against the fetched current branch.

The commented helper and first DAG proof step relied on private declarations of the
old `Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections` module.
That file is now a re-export of its upstream counterpart; `import all` on the wrapper
is not a stable way to access the upstream private helpers. The repair avoids them.
The first attempted direct upstream import also found its compiled artifact missing
from the published build, while the old Sheaf artifact was available. The final proof
uses ordinary imports and public declarations whose signatures were checked in the
current shared upstream sources, so it does not rely on either private-module layout.

The two direct consumers are
`Sheaf.AlgebraicGeometry.CoherentKernelIdealProductCompletionZero` and
`Sheaf.AlgebraicGeometry.FormalCompletionPushforwardLimitAppBijective`. Both use the
same unchanged existential quotient/limit interface. No consumer adaptation is needed.
The unit route of `sk-thm-p1` is retained, and this auxiliary node is not itself a
realization of a unit statement or step. No new nodes or disputed statements.

## Earlier second reading (a previous round; superseded)

1. **Unchanged interface.** Compared the delivered module with the repository version. The public
   imports, target theorem signature, existing declarations, and definitions are unchanged; the
   only code changes are proof implementation and proof-only imports. The target statement still
   has exactly the original hypotheses and conclusion.

2. **Proof and axioms.** Compiled the module with `lcompile.py` successfully and inspected the
   complete proof. It contains no `sorry`, axiom, unsafe, opaque, extern, or hollow definition.
   The quotient helper constructs its isomorphism from the explicitly computed kernel and
   surjectivity, and the completion isomorphism is obtained from the stable-ranges theorem.
   The delivery probe is required to confirm that the resulting declarations use only the
   permitted axioms.

3. **Statements and duplication.** The private helper is an intermediate kernel-and-quotient
   reduction, not a restatement of the target. Its assumptions and conclusion are exactly what
   the finite-level argument needs. I checked the public tensor-section theorem and cokernel-image
   theorem used by the proof; no new public statement or split-off hole is introduced. Search of
   the local library and the requested msearch queries found no duplicate affine completion
   comparison theorem.

4. **Route and pruning.** The proof keeps the unit route through affine ideal powers, tensor
   sections, cokernel-image exactness, and stable adic ranges. It removes dependence on the old
   private `multiplication_range` and `product_qc` helpers while retaining all mathematical proof
   dependencies. The DAG proof and `proof_deps` now record the public tensor theorem and the
   cokernel-image calculation actually used.

5. **DAG agreement.** Checked the sandbox node against the Lean proof: its first step records the
   tensor-section and cokernel-image calculations, the later steps record transition and stable
   range arguments, and `proof_deps` is the union of the declarations used. The unit
   `sk-thm-p1` route remains intact.

Changed in this second reading: corrected the node metadata to match the repaired public proof
route, and added this review record. No theorem statements, definitions, or split-off nodes were
changed.

## Second reading by P4

1. **Interface unchanged.** I compared the sandbox module with the repository version. The target
statement, all existing declaration signatures, definitions, and public imports are unchanged;
the only module edits are proof code and proof-only imports. The node's target statement is also
unchanged.

2. **Proof and axioms.** I compiled the complete module with `lcompile.py`, and separately
compiled a copy with `#print axioms AlgebraicGeometry.formalCompletion_affine_sections`.
There are no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow
definitions. The reported axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The private quotient helper is a concrete first-isomorphism-theorem construction, and the
completion isomorphism is obtained from the stated stable-ranges theorem.

3. **Statements and duplication.** The restored private `quotient_sections_iso` theorem is a
strict finite-level reduction: it identifies one affine quotient and its projection equation,
so it does not restate the completion target. Its proof uses only the public tensor-section,
ideal-times, and cokernel-image declarations; no new public theorem or split-off statement was
added. I checked the local library for duplicate affine completion comparison declarations.

4. **Route and pruning.** The proof preserves the unit route through ideal powers, affine tensor
sections, cokernel-image exactness, and stable adic ranges. It removes the former `import all`
visibility dependency and computes the multiplication range from public declarations. All
remaining imports and all five recorded proof dependencies are used by the final proof; no
additional node or module can be pruned.

5. **DAG agreement.** I checked each proof step and dependency against the Lean source. The node
records the tensor/image range calculation, quotient construction, transition argument, and
stable-range completion argument in that order, with the corresponding proof dependencies and
origin. The `sk-thm-p1` unit route is retained, and no unit statement or step is bypassed.

Changed in this second reading: added this review record. No theorem statements, definitions,
split-off nodes, or additional modules were changed.
