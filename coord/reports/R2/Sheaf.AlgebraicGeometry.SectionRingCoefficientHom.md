## What changed

Added `SectionRingCoefficientData`, introducing coefficient-function data with zero, one,
addition, multiplication, and numerator identities. Proved
`exists_sectionRing_coefficient_hom` by constructing a `RingHom` from that data and removed
no imports from the target module.

## Proved and sorry left

Closed `exists_sectionRing_coefficient_hom` in `SectionRingCoefficientHom.lean`.
Left `exists_sectionRing_coefficient_data` as a deliberate intermediate theorem with `sorry`
in `SectionRingCoefficientData.lean`; node `lem-sc-section-ring-coefficient-data`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The DAG plan requires substantial coefficient well-definedness and arithmetic. These were split
into one strictly lower coefficient-data theorem so the target proof can be checked as a genuine
RingHom construction.

## New nodes

`lem-sc-section-ring-coefficient-data`: coefficient function data used to construct the target
ring homomorphism.

## Second reading by R2

1. Compared the delivered target module with the repository version. The theorem
   signature is byte-for-byte unchanged; the only interface change is the private
   proof import of `SectionRingCoefficientData`.
2. Compiled both delivered modules with `lcompile.py --all`. The target proof has no
   errors, and the only remaining `sorry` is the named intermediate theorem
   `exists_sectionRing_coefficient_data`.
3. Checked the split statement against the target. It is a lower-level coefficient
   function statement: it supplies the arithmetic fields and numerator identity,
   while the target separately packages those fields into a `RingHom`. The statement
   is true under exactly the target hypotheses and has its own node and source
   docstring; no existing Mathlib or library declaration duplicates it.
4. Checked pruning and imports. The proof uses the coefficient-data module and the
   target's original imports; no imported module or node is unused, so none is
   removed. The unit route remains recorded in the unit and node metadata.
5. Checked the DAG records against the Lean proof. The target node now records the
   coefficient-data node as a proof dependency and the data node records its own
   theorem and source. No statement or definition was changed.

Changed the target node's proof metadata and added this review record; no Lean
statement or definition was changed.
