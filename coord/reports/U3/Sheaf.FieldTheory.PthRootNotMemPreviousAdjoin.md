## What changed

Proved `IntermediateField.pth_root_not_mem_previous_adjoin` in
`Sheaf.FieldTheory.PthRootNotMemPreviousAdjoin`, preserving its signature byte for byte.
Added only the proof imports `Mathlib.Algebra.CharP.Algebra` and
`Mathlib.Algebra.CharP.Lemmas`; the original public imports are unchanged.

The proof uses field-adjoin induction. For each element x of the preceding root field,
it constructs b in k such that x^p = algebraMap(b) and D(b) belongs to the span of the
preceding differentials. The generator, base-field, sum, product and inverse cases
follow from Frobenius, the power Leibniz formula and the inverse Leibniz formula.
Injectivity identifies b with the final a, and `LinearIndependent.notMem_span` supplies
the contradiction. This avoids the finite-dimensional monomial-span detour.

## Proved and sorry left

Hole closed: `IntermediateField.pth_root_not_mem_previous_adjoin`
(node `lem-weil-pbc-pth-root-not-mem-previous-adjoin`). Proved 1 of 1 original holes.
Holes added: none. Sorry left in the delivered module: none. Split off: none.
The scratch axiom check shows only `propext`, `Classical.choice`, and `Quot.sound`.
This is a complete proof, not a decomposition.

The first worker's proposed `IntermediateField.pth_root_mem_forces_differential_dependence`
was removed with its undelivered module and node; it contributes no new hole.

## No longer needed

The old proof dependency `lem-weil-pbc-finite-dimensional-domain-is-field` is no longer
used. Its Mathlib declaration `fieldOfFiniteDimensional` is unnecessary: field-adjoin
induction handles inverses directly. This is the only old proof dependency pruned.
No original import was removed: the three public imports are needed by the signature.

The unlanded `Sheaf.FieldTheory.PthRootMemForcesDifferentialDependence` module and
`lem-weil-pbc-pth-root-mem-forces-differential-dependence` node were removed from the
sandbox delivery, together with the corresponding proof import.

## Where the brief, the DAG or earlier work was wrong

The first worker's new theorem was the contrapositive of the item itself; applying it
to the independence assumption moved the whole hole without a genuine reduction.
Its docstring did not give a natural-language proof, its search records were empty,
and its node's Lean statement was an ellipsis rather than a verbatim signature.
The original item's node had not been updated to the proposed proof.

A shorter route is available through Mathlib field-adjoin induction. The differential
span calculation is closed locally, so there is no need to repair or retain the new
split node. The existing node now records the actual proved route.

## Second reading by U3

1. PASS. Compared the delivered file with the repository by diff and asserted
   byte-identical theorem signatures. No existing definition, visibility, signature,
   public import, or target statement changed; no change record is required.
2. PASS. Compiled the complete proof locally with `lcompile.py`. There are no sorries,
   axioms, unsafe/opaque declarations, implementation overrides or hollow definitions.
   A scratch copy with `#print axioms IntermediateField.pth_root_not_mem_previous_adjoin`
   reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
3. PASS after repair. Rejected and removed the contrapositive restatement and its node.
   No new statements or holes remain. Searched the local library with differential,
   Frobenius and span vocabulary and Mathlib via the authorized Loogle, LeanSearch and
   grep wrappers. Loogle found `LinearIndependent.notMem_span`; LeanSearch was unavailable.
   Read the actual field-adjoin and derivation lemmas. The induction also handles the
   empty preceding family (n=0), zero witnesses and zero inverses; it assumes no
   independence of the preceding roots, monomial basis or algebraic closure.
4. PASS. The fully proved induction is shorter than the planned finite-dimensional
   span argument. All unused old proof dependencies are listed above. The two added
   imports are proof-only and directly supply characteristic transfer and Frobenius
   additivity. The original public imports supply objects in the unchanged signature.
   Read `dag/units/sk-thm-p1.json`: this node is not a unit statement or realized step;
   the change is below the unit level, preserving the Popescu/07DZ route and all unit
   realizations. Read Stacks Tag 07DZ and retained its differential-span contradiction.
5. PASS after repair. Updated only the existing node's `proof`, `proof_deps` and
   `proof_origin` to the field-adjoin induction and independence contradiction; checked
   all other fields against the repository. No new nodes are delivered.

Changes by the second reader: replaced the whole contrapositive delegation by a direct
proof, removed the proposed split module/node, added minimal proof-only Mathlib imports,
pruned the finite-dimensional-domain dependency, and corrected this report and the DAG
proof metadata.
