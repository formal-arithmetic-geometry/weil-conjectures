## What changed

Completed `Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct` in
`Sheaf.FieldTheory.GeometricallyReducedExtensionSeparable`, preserving its signature,
visibility, universes, original public imports, and existing docstring.

The proof applies reducedness to `ULift.{v} (AlgebraicClosure k)`, so the auxiliary field
has precisely the universe permitted by `hred`. A relation among p-th powers determines
a tensor whose p-th power vanishes; reducedness and flat scalar-extension independence
force all the coefficient roots to vanish. The criterion passes along the inclusion of
each finitely generated intermediate field. Mathlib's theorem tagged 030W (2) => (1)
then produces its separating transcendence basis.

Added proof-only imports of `Mathlib.FieldTheory.SeparablyGenerated`,
`Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`, `Mathlib.RingTheory.Flat.Basic`,
and `Mathlib.Algebra.Field.ULift`. Updated the existing node's proof and dependencies
to match the compiled proof. No interface changes or forced adaptations.

## Proved and sorry left

Closed 1 original hole:
`Algebra.isSeparableExtension_of_forall_isReduced_tensorProduct`
(node `lem-weil-pbc-geometrically-reduced-extension-separable`).
No holes added, no sorries left, and no split-off statements.

Single-file compilation is clean. The explicit axiom check reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Pruned proof dependency `lem-weil-pbc-vector-space-basis-through-vector`:
Mathlib's `Module.Flat.linearIndependent_one_tmul` supplies scalar-extension
independence directly. This node is a Mathlib leaf, not an additional Sheaf module;
no project module is asserted globally unreachable. All other original dependencies
remain used. No original import removed. The temporary proof-only import
`Mathlib.Algebra.CharP.Lemmas` was removed as redundant after compilation; its
Frobenius results are already available through the retained imports.

No construction of the subfield `k^{1/p}` is needed: the all-field-extensions
hypothesis already covers the algebraic closure. The original docstring describes
the source's smaller-field variant; the updated DAG and proof comments record the
implemented variant. The unit's statement and realized steps remain untouched.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable definition found. The planned basis-extension step
was unnecessary because Mathlib proves scalar-extension independence directly.
Searching Lean Finder and Loogle confirmed `Module.Flat.linearIndependent_one_tmul`;
local Mathlib search supplied the separating-basis criterion and root-existence lemma.
The proof uses no unproved project theorem.

## Second reading by Q2

1. Compared the delivered module with the repository version. The theorem signature and
   all existing declarations are byte-for-byte unchanged; only proof-only imports and the
   proof body differ.
2. Compiled the module with `lcompile.py`; it is clean, contains no `sorry`, `axiom`,
   `unsafe`, `opaque`, `implemented_by`, or `extern`, and the axiom check is limited to
   `propext`, `Classical.choice`, and `Quot.sound`.
3. Checked the proof route and node. The Frobenius/tensor argument is valid, the
   universe-lifted algebraic closure satisfies the stated hypothesis, and the final
   Mathlib criterion is applied with exactly the required finite-type and independence
   hypotheses. No new statement was split off.
4. Checked pruning and imports. The unused basis-extension dependency was removed from
   the node's proof dependencies; all retained imports and dependencies are used, and the
   unit route and realized steps remain intact.
5. Searched the project and Mathlib for duplicate declarations and checked the node's
   statement, proof, dependencies, and origin against the Lean proof. No discrepancy or
   false statement was found.

Changed only the proof, proof-only imports, matching DAG proof metadata, and this report;
no statement, definition, or target was changed.
