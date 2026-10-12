## What changed

Proved `geometricallyRegular_of_directed_subfields` in
`lean/Sheaf/RingTheory/GeometricRegularitySubfields.lean`. The proof unfolds geometric
regularity, obtains a finite presentation of each finite purely inseparable test field,
uses the new coefficientwise model theorem, applies finite purely inseparable scalar
descent, and transports regularity through tensor cancellation and ring equivalences.
Added `Sheaf.FieldTheory.FinitePresentationSubfieldModel`, whose theorem
`Algebra.exists_subfield_model` is proved completely by finite presentation, directed
coefficient descent, polynomial scalar extension, quotient tensor base change, and
`ULift`.

## Proved and sorry left

Closed the original sorry `geometricallyRegular_of_directed_subfields`. The new theorem
`Algebra.exists_subfield_model` is also proved with no sorry. The proof uses the existing
sorry-backed declaration `Algebra.TensorProduct.finite_purelyInseparable_of_tensorProduct`
as a stated dependency; no new sorry remains in this delivery. Holes closed: 1; holes added: 0; split-off
holes: 0. The main theorem still has `sorryAx` transitively through that existing
scalar-descent dependency, so this is a proof from the existing planned dependency,
not a claim that the target's entire axiom closure is finished.

Both delivered modules compile without warnings locally. The model theorem handles
zero algebras and presentations with no variables or relations; its finite-set
induction explicitly uses nonemptiness for an empty coefficient set. `ULift` puts the
model in exactly the universe that geometric regularity tests. The dry run checks local compilation, the axiom probe, and preflight; server
compilation is disabled by the launcher under the current project settings.

## No longer needed

No original imports were removed, and no library module is pruned. The second
reader removed the newly added redundant proof import
`Mathlib.RingTheory.TensorProduct.Maps` from the main module; the model module
already supplies this API through its proof imports. The existing
`Sheaf.FieldTheory.FinitePurelyInseparableScalarDescent` import remains necessary.
`Mathlib.FieldTheory.IntermediateField.Basic` and `Sheaf.RingTheory.GRing` retain their
existing public status, so downstream statements see the same interface.

The original direct edge to `lem-weil-pbc-finite-type-algebra-noetherian` is replaced by
`lem-weil-pbc-finite-type-noetherian-finite-presentation`, the Mathlib leaf giving the
needed finite presentation directly. Polynomial scalar extension and quotient base
change remain needed in the proved model module; their edges move under its new node
and are not pruned. Tensor cancellation and finite purely inseparable scalar descent
remain direct dependencies of the original theorem. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The DAG's five prose steps correctly describe the argument, but the original module
had no Lean declaration packaging the finite-presentation and coefficient descent. I made that construction an explicit strictly smaller
intermediate theorem so the top-level proof can be checked by Lean. The Stacks proof's
printed identity is interpreted as `k' ≅ k ⊗[K i] k_i'`, as already recorded in the node.

## New nodes

`lem-weil-pbc-finite-presentation-subfield-model` records the finite-presentation model
construction and is stated by `Algebra.exists_subfield_model` in
`Sheaf.FieldTheory.FinitePresentationSubfieldModel`.


## Second reading by H2

1. PASS: compared the complete main module with the repository version. The sole
   existing declaration's signature and docstring are byte for byte unchanged;
   only its proof and private proof imports change. The other module and its
   declaration are new. No definitions or existing statements change, so no
   change record is needed.
2. PASS: compiled both delivered modules locally in import order without errors
   or warnings. Neither file contains `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, or `extern`, and neither introduces a definition. Scratch
   copies with `#print axioms` show only `propext`, `Classical.choice`, and
   `Quot.sound` for `Algebra.exists_subfield_model`; the main theorem additionally
   has `sorryAx`, through the explicitly retained existing scalar-descent theorem.
   The descended model is constructed as a polynomial quotient and ULift using
   proved finite-presentation and coefficient-lifting results. No arbitrary data
   are extracted from an unproved existence theorem.
3. PASS: there are no split-off holes. Read the proved new model theorem in full:
   it is strictly the coefficient-descent portion of the original argument and
   does not assume geometric regularity or assert the original conclusion.
   Checked empty generator and coefficient sets, zero algebras, zero variables,
   singleton families, and the required universe `max u w`. The finite-set
   induction correctly uses `Nonempty I` for the empty case. Independent
   leanfinder, loogle, and grep searches with filtered-union/coefficient-field
   queries, plus searches of Sheaf and upstream sources, found no exact existing
   directed-subfield model theorem. Mathlib's `Presentation.ModelOfHasCoeffs` and
   `tensorModelOfHasCoeffsEquiv` package the same quotient construction after a
   coefficient ring has been selected; upstream's
   `exists_fg_subalgebra_isPushout` chooses a finitely generated integer
   subalgebra instead. Neither supplies selection of a member of this family.
   The delivered proof already uses Mathlib's finite presentation, polynomial
   scalar extension, and quotient tensor equivalences directly.
4. PASS: followed the main proof downward from the test extension to the proved
   model, existing purely inseparable scalar descent, and tensor cancellation.
   All retained imports supply statement or proof APIs. Removed the redundant
   newly added `Mathlib.RingTheory.TensorProduct.Maps` import and recompiled.
   The old direct finite-type-Noetherian edge is replaced by the finite-
   presentation leaf; the old polynomial and quotient edges move to the model
   node and remain in the argument. These changes are all listed above. Read
   `dag/units/sk-thm-p1.json`: neither this node nor the replaced Noetherian leaf
   realizes a unit statement or step; the unit route is unchanged.
5. PASS: read both delivered nodes and their cited leaves. Their proof steps,
   `proof_deps` (the union of step uses), and `proof_origin` match the Lean proof.
   The new node has the required source, complete mathematical construction,
   searches, creation and blueprint provenance, chapter/unit, and Lean record.
   Existing statement and statement-dependency fields are unchanged.

Second-reading changes: removed one redundant newly added proof import; clarified
that the current dry-run tool uses local compilation rather than server
compilation; added this review. No proof body, statement, definition, or DAG route
needed repair. Original holes closed: `geometricallyRegular_of_directed_subfields`
(1 of 1); new holes added: none; split-off holes: none; modules pruned: none.
