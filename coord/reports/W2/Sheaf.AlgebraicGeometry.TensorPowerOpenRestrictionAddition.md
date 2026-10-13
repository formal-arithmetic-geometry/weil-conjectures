## What changed

Proved `AlgebraicGeometry.Scheme.Modules.openRestrictionTensorPowIso_inv_add` in
`Sheaf.AlgebraicGeometry.TensorPowerOpenRestrictionAddition`, preserving its statement,
visibility, docstring and imports. Six proved private helpers implement the existing plan:
tensor extensionality, local triple-tensor extensionality, the inverse tensor comparison
formula, its successor power formula, compatibility with equality transport, and induction
of the addition diagram as a sheaf-morphism equality.

The triple-tensor extensionality proof follows the proved private helper in
`Sheaf.AlgebraicGeometry.ModulePullbackTensorCoherence`: the image sieve of the inner tensor
sheafification is covering, sectionwise tensor induction proves equality on that sieve,
and separatedness gives equality on the original open. This avoids assuming that pure
tensors generate global sections. The zero case uses the actual scalar action and unit
comparison; the successor case uses the associator section formula and the induction
hypothesis. Equality transports are handled by equality elimination and cancellation.
Elaboration options are scoped to individual declarations.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.openRestrictionTensorPowIso_inv_add`
(node `lem-sc-tensor-power-open-restriction-addition`). All six private helpers are proved.
No `sorry` remains in the item; no new holes, statements with `sorry`, or modules were added.
This is a proof, not a decomposition. Local compilation succeeds without warnings.

## No longer needed

No import or module was removed. Removed the direct proof dependency
`lem-pc-sites-sheaf-tensor-bilinear-universal`: local extensionality uses Mathlib's
sheafification adjunction and covering image sieves directly. This node remains a
transitive dependency through the existing restriction tensor comparison, so no module
is pruned from the import closure. The remaining direct dependencies are tensor powers
and addition, recursive open-restriction comparisons, and the tensor comparison.
The module `Sheaf.AlgebraicGeometry.ModulePullbackTensorCoherence` was read as an example
but is not imported or needed by this proof. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The original plan is realized directly; separate naturality
and associator-coherence declarations are unnecessary because the induction diagram is
checked on local triple tensors itself. There are no statement, definition, interface,
unit-route, or forced-adaptation changes.

## Second reading by W2

1. PASS: compared the complete delivered module with the repository using diff. The sole
   existing public theorem's signature, visibility, docstring, and public import are
   byte-for-byte unchanged. The six additional declarations are private proved helpers;
   no definition or public interface changes, hence no change record is needed.
2. PASS: locally compiled the module without errors or warnings (12.1 seconds). Scanned
   the entire module: no sorry, axiom, unsafe, opaque, implemented_by, extern, or hollow
   definition. A scratch copy prints axioms for all six helpers and the public theorem;
   only propext, Classical.choice, and Quot.sound occur. The definition of the chosen
   tensor comparison specifies its inverse on every pure tensor, determining it uniquely
   by tensor extensionality; it is not an arbitrary existence witness.
3. PASS: there are no split-off statements or new holes to review. All helpers are proved.
   Checked degree zero (including both exponents zero), successor degree, zero modules,
   and empty opens: the scalar/unitor and local sheaf arguments impose no extra hypothesis.
   Searches by extensionality, addition and restriction in Mathlib, upstream, and Sheaf
   found no accessible theorem replacing the recursive addition argument. Existing
   matching extensionality helpers are private and cannot be imported for use.
4. PASS: the proof realizes the original induction directly; no unresolved lemma is
   introduced. The sole public import supplies types and definitions used in the public
   statement and must remain public. Checked dag/units/sk-thm-curveestimate.json: its
   realized statement thm-sc-proper-cohomology and its empty step list are unchanged, and
   this item is below the unit level. No module is pruned; the removed direct DAG
   dependency remains transitively used by restriction tensor comparison.
5. PASS after correction: updated the existing node's proof and proof_deps to record
   Mathlib sheafification extensionality, covering-sieve descent, scalar action, and
   induction as actually written. The retained agent proof_origin correctly attributes
   the expanded Stacks argument. No new nodes are needed.

Second reading changed only the DAG proof plan and direct dependencies, clarified
No longer needed, and added this review. The Lean proof was read and retained unchanged.
