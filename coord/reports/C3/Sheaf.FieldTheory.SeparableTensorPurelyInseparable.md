## What changed

Proved `separableTensor_purelyInseparable_isField` in
`Sheaf.FieldTheory.SeparableTensorPurelyInseparable`, with its signature unchanged.
Added the proof-only import `Mathlib.FieldTheory.PurelyInseparable.Tower`.
The second reading removed the redundant direct imports
`Mathlib.FieldTheory.LinearDisjoint` and
`Mathlib.LinearAlgebra.Dimension.Constructions` (both provided transitively by Tower).
`Mathlib.FieldTheory.PurelyInseparable.Basic` supplies the statement vocabulary.
Fieldness follows from the common-overfield criterion and linear disjointness of
separable and purely inseparable images. The tensor Frobenius-power lemma gives
pure inseparability; the base-change finite-module instance and dimension formula
give the final two clauses. Updated the existing node's proof and proof origin to
match this implementation. The unit's statement and realized steps are untouched.

The module compiles without warnings through `lcompile.py`. No new modules,
statements, or definitions are delivered. The only interface change is import
visibility, recorded in
`coord/changes/separableTensor_purelyInseparable_isField-imports.md`.
The unchanged direct importer compiles against the reviewed module; no forced
adaptation is needed.

## Proved and sorry left

Closed the sole hole, `separableTensor_purelyInseparable_isField`
(node `lem-weil-pbc-separable-tensor-purely-inseparable-field`).
Holes closed: 1. Holes added: 0. Sorries left: none.
The proof uses only proved Mathlib declarations.

## No longer needed

Removed the redundant direct imports `Mathlib.FieldTheory.LinearDisjoint` and
`Mathlib.LinearAlgebra.Dimension.Constructions`; their lemmas remain available
transitively through the proof-only Tower import. No DAG nodes
or modules are pruned. Both existing proof dependencies remain used. The explicit compositum construction and the manual tensor-basis and
Frobenius calculations in the plan are supplied by proved Mathlib lemmas instead.
No additional statement module is needed.

## Where the brief, the DAG or earlier work was wrong

The earlier Mathlib search missed
`IsPurelyInseparable.exists_pow_pow_mem_range_tensorProduct_of_expChar` in
`Mathlib.FieldTheory.PurelyInseparable.Basic`, which supplies the tensor power
calculation directly. `IntermediateField.LinearDisjoint.isField_of_forall`
also avoids constructing a common algebraic overfield explicitly. No mathematical
statement correction was needed. Characteristic zero is covered by exponential
characteristic 1 in the Mathlib power criterion; no positive-characteristic
assumption was added.

## Earlier second reading (a previous round; superseded)

1. **Signatures and visible changes — pass.** Diffed the sole delivered module
   against the repository. The existing theorem signature, universes, hypotheses,
   conclusion and visibility are byte for byte unchanged. There are no definitions
   or new declarations. The import visibility correction is deliberate and recorded
   in `coord/changes/separableTensor_purelyInseparable_isField-imports.md`.
2. **Proof and axioms — pass.** Independently compiled the module with lcompile.py
   without errors or warnings. A scratch copy with `#print axioms
   separableTensor_purelyInseparable_isField` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. There are no sorries, axioms, unsafe or
   opaque declarations, external implementations, or hollow definitions. The local
   field structure comes from the proved IsField property, whose inverses are unique.
3. **Split statements — pass, none.** No statements were split off and no holes
   added. Read the Mathlib common-overfield criterion, separable/purely inseparable
   linear-disjointness lemma, tensor Frobenius lemma, and dimension formula. The
   argument covers characteristic zero (exponential characteristic 1), positive
   characteristic, either trivial extension, and infinite separable algebraic k'.
4. **Shortest route, imports and unit — pass after import repair.** Searched the
   library and Mathlib by tensor/base-change and purely inseparable terminology;
   the existing proof uses the direct proved ingredients, without additional
   statement modules. Removed redundant LinearDisjoint and privatized the
   proof-only dimension import. Both old proof dependency nodes remain used and
   no modules are pruned. Read sk-thm-p1's realized statement and steps: this node
   is below their level, and no realized node or unit route is bypassed. The sole
   direct importer GeometricRegularitySeparableExtension compiles unchanged
   against the reviewed module in a scratch compilation set; the remaining
   downstream users are behind that importer's private edge.
5. **DAG agreement — pass.** Diffed the existing node: only proof and proof_origin
   change. Its three steps describe fieldness, pure inseparability, and finite
   dimension in the order used in Lean; proof_deps remains their union. Both
   dependencies are Mathlib leaves matching the declarations used. No new nodes,
   statement changes, or unit changes occur.

Changed in this reading: removed the redundant direct LinearDisjoint import,
made Dimension.Constructions proof-only, updated the proof docstring, and recorded
and checked downstream effects of import visibility. The mathematical proof was
kept unchanged. Holes closed: separableTensor_purelyInseparable_isField (1).
Holes added: none (0).

## Earlier second reading (a previous round; superseded)

1. **Visible changes — pass.** Compared every delivered module with the repository.
   The sole existing theorem signature is byte-identical, including universes,
   hypotheses and all four conclusions. No definitions or statements were added.
   Public import removals are declared in the import change record.
2. **Proof — pass.** Independently compiled the module and a scratch axiom probe
   through lcompile.py. The theorem uses exactly propext, Classical.choice and
   Quot.sound. No sorry, forbidden declarations or hollow definitions remain.
   IsField.toField constructs the uniquely determined field operations from a
   proved property, not an arbitrary witness of an unproved existence statement.
3. **Split statements — pass, none.** No new statements or holes. Read the actual
   Mathlib common-overfield criterion, image transport, linear-disjointness,
   tensor-power criterion and dimension formula. Checked characteristic zero
   (exponential characteristic 1), positive characteristic, trivial extensions,
   and the absence of any finiteness requirement on the separable extension.
4. **Route and pruning — pass after repair.** Independently searched Mathlib and
   both library roots using base-change and inseparable/tensor vocabulary. The
   proof uses direct proved Mathlib ingredients. A scratch compile established
   that Dimension.Constructions is also redundant through Tower; removed its
   direct import. Both old proof_deps remain used, so no DAG nodes or modules are
   pruned. Read sk-thm-p1 and its realized record: the item is below the realized
   steps and bypasses no unit. Compiled the current unchanged direct importer,
   GeometricRegularitySeparableExtension, against the delivered module in a
   separate scratch module set; no adaptation is needed.
5. **Nodes — pass.** Diffed the sole node: only proof and proof_origin changed.
   Its steps follow fieldness, pure inseparability and finite dimension exactly
   as Lean does; proof_deps is the union of uses. Both dependencies are existing
   Mathlib leaves. No new nodes, unit edits or statement changes.

Changed in this reading: removed the remaining redundant direct dimension import
and updated its change record and report. Kept the mathematical proof unchanged.
Hole closed: separableTensor_purelyInseparable_isField (1 of 1).
Holes added: none (0); split off: none; DAG modules pruned: none.

## Second reading by C3

1. **Visible changes — pass.** Independently diffed the sole delivered Lean module
   against the repository. Its existing theorem signature is byte for byte unchanged;
   no declarations or definitions were added. The deliberate removal of two public
   imports is fully recorded in the existing import-visibility change record.
2. **Proof and axioms — pass.** Compiled the module and the complete delivery with
   lcompile.py without errors or warnings. Compiled a scratch copy with the axiom
   probe: exactly `propext`, `Classical.choice`, and `Quot.sound`. No sorry or forbidden
   declaration occurs. The field structure is obtained from proved IsField, whose
   operations are determined, not from an unproved arbitrary existence witness.
3. **Split statements — pass, none.** No new statements or holes are delivered.
   Read the actual common-overfield criterion, the image linear-disjointness theorem,
   and the tensor exponential-characteristic lemma in the pinned Mathlib. The proof
   covers characteristic zero (q = 1), positive characteristic, trivial extensions,
   and separable algebraic extensions of infinite degree.
4. **Route, imports and pruning — pass.** Independently searched with radicial and
   scalar-extension terminology through msearch leanfinder, and searched both library
   roots and Mathlib for tensor/field/purely-inseparable declarations. No shorter
   complete result was found. Basic supplies the signature vocabulary; Tower is needed
   only for the proof and is private. Both original proof_deps remain used, so the
   No longer needed section correctly lists no pruned DAG nodes or modules. Read
   sk-thm-p1's realized record: this node is below its steps and bypasses none.
   A separate scratch module set compiled the current unchanged sole direct importer,
   GeometricRegularitySeparableExtension, against the delivered module. Its import
   edge is private, so no removed reexport reaches the transitive users through it.
5. **DAG agreement — pass.** Independently diffed the sole delivered node. Only proof
   and proof_origin change; the three steps match the Lean argument and proof_deps
   is their union. Verified both dependencies against their Mathlib leaf records.
   No new nodes, statement changes, or unit changes are delivered.

Changed in this reading: added this required current second-reading section after
independent verification; no Lean or DAG repair was needed. The dry run initially
rejected the report because earlier readings were superseded and the exact required
heading was absent. Hole closed: separableTensor_purelyInseparable_isField (1 of 1).
Holes added: none (0); split off: none; pruned DAG modules: none.
