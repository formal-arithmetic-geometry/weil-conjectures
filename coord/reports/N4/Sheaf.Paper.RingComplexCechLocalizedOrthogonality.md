## What changed

Replaced the sorry in `AlgebraicGeometry.ringComplex_cech_localized_orthogonality`
by a proof from source cohomology torsion and a proved generic localization lemma.
The proof unpacks the shift-closure witness and transports zero through its
isomorphism. The original statement, binders, universes and public imports stay
unchanged.

Added `Sheaf.Paper.PowerTorsionLocalizedShiftHom`, proving
`AlgebraicGeometry.power_torsion_localized_shift_hom`. It constructs the
point-evaluation equivalence, exact extension and restriction of scalars, the
localized coefficient action, the derived adjunction, and the single-complex
comparison. No Cech-model assumption occurs in this theorem.

Added `Sheaf.Paper.RingComplexCechCohomologyPowerTorsion` for the remaining
source-only step. Its statement says each cohomology class is killed by some
power of an ideal element. It has no coefficient module or derived Hom conclusion.
Updated the item node to describe this route. No shared definition or signature
was changed, and no existing module besides the item was edited.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ringComplex_cech_localized_orthogonality`.
Proved the new generic theorem
`AlgebraicGeometry.power_torsion_localized_shift_hom` without sorry.

Added exactly one hole:
`AlgebraicGeometry.ringComplex_cech_cohomology_power_torsion`, node
`lem-weil-pbc-ring-complex-cech-cohomology-power-torsion`.
This is a decomposition: one upper hole closed, one strictly smaller source
cohomology hole added, net zero holes. The parent has zero remaining local holes.
The remaining theorem has its complete contraction/localization proof in words
and includes the zero ring, zero or nilpotent element, repeated-generator and
empty-initial-list cases. The coefficient action is constructed from the proved
module-localization identity property; no data is chosen from a sorry theorem.

Validation: all three modules compile together through `lcompile.py --all`
(10.4 s, 2.9 s and 3.7 s). The generic theorem's `#print axioms` output is
exactly `propext`, `Classical.choice`, `Quot.sound`; the diagnostic command was
removed afterwards. The original parent signature and public imports are
byte-identical, and node signatures and dependency unions were checked.

## No longer needed

No existing module or mathematical dependency is pruned from the import closure.
The original direct dependencies on localization flatness and exact derived
adjunction are now used inside the generic theorem, rather than directly by the
item. The Cech-model and derived-category definitions remain needed. No unit
statement or realized unit-proof step is bypassed.

Removed the exploratory `Mathlib.CategoryTheory.Triangulated.Orthogonal`
import from the new generic module and the unused
`Mathlib.Algebra.Homology.DerivedCategory.HomologySequence` public import from
the source-torsion module. Replaced the generic module's exploratory public
`Sheaf.Paper.RingComplexCechData` import by
`Sheaf.Algebra.Homology.RingHomExtensionDefs`.
The new generic module does not need ordered Cech definitions or orthogonality
predicates in its statement; its public imports are limited to the ring-site
module definitions and the derived-category API. No speculative Koszul or tensor
Cech imports were added: the available torsion/acyclicity declarations do not
supply a comparison with an arbitrary coordinate-model witness.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The previous proof plan combined two substantial
arguments in one hole: the ordered-localization contraction and the exact derived
adjunction. This delivery formalizes the entire latter argument and the final
transport, leaving only the source cohomology assertion. The remaining lemma is
not the original orthogonality statement under another name.

## New nodes

`lem-weil-pbc-ring-complex-cech-cohomology-power-torsion` records the source-only
cohomology assertion, in
`lean/Sheaf/Paper/RingComplexCechCohomologyPowerTorsion.lean`. It is the first step
of the original proof, followed by the module-localization zero criterion.

`lem-weil-pbc-power-torsion-localized-shift-hom` records the proved generic exact
localization/derived-adjunction argument, in
`lean/Sheaf/Paper/PowerTorsionLocalizedShiftHom.lean`.

No change record is needed: existing statements and definitions are unchanged.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
