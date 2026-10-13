## What changed

Proved `AlgebraicGeometry.Scheme.Modules.inverseImageCohomology_comp` in
`Sheaf.AlgebraicGeometry.Cohomology.InverseImageCohomologyComposition`, preserving its
statement and visibility. The private, proved helper `constant_adjunct_invImage`
characterizes the inverse constant comparison by its adjunct on global sections.
Adjunction uniqueness and the composite-unit identity prove constant-comparison coherence;
the existing, proved `Abelian.Ext.exactFunctorCompositionComparison` and Mathlib Ext
composition lemmas then give the cohomology equality. Both existing imports are used and
unchanged. Updated the node's proof description and proof origin to record the actual Lean
argument. No definitions, existing signatures or public imports changed.

The proof follows both steps of the node's original plan. The node is below the unit level;
none of the realized statement or proof steps of `sk-thm-p1` is bypassed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.inverseImageCohomology_comp`
(node `lem-pbc-inverse-image-cohomology-composition`).

No holes remain in the item. No holes were added or split off. The private helper is proved.
Local compilation passed without warnings. `#print axioms` reports exactly `propext`,
`Classical.choice` and `Quot.sound`, with no `sorryAx`.

## No longer needed

No imports or modules removed: `InverseImageCoefficientComposition` supplies the definition
`invImageComp` used in the unchanged statement, and `ExtExactFunctorCompositionComparison`
supplies the Ext comparison used in the proof. `coefficientUnit_comp` itself is not used;
the node `lem-pc-coefficient-unit-composition` remains needed for its composition comparison
definition. No whole DAG node or module can be pruned by this proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The existing DAG's two-step adjunction/Ext plan is realizable.
The source library's private adjunct calculation in `CechInverseImageDegreeZero` provides a
useful model, but its module is not imported: the elementary calculation here omits the
identity restriction map at the top open and is proved directly from adjunction lemmas.
The full theorem applies without any flatness, coefficient or nonempty-scheme assumptions.

## Second reading by T4

1. Compared the delivered module with the repository version. The theorem statement and all existing declaration signatures are byte-for-byte unchanged; only the proof and a private helper were added.
2. Compiled the module successfully with `lcompile.py`; no `sorry`, forbidden declarations, or warnings remain. `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.
3. Searched the library and Mathlib for duplicate results. The private adjunct calculation is local and no new public statement or split-off hole was added; the existing node remains the exact target statement.
4. Checked the proof route and imports. The proof uses the declared inverse-image coefficient composition and Ext comparison dependencies, and preserves the unit route through the constant comparison and Ext composition. Both imports are needed.
5. Checked the DAG proof steps and dependencies against the Lean proof. The node records the adjunct and Ext steps actually used; no realized unit step is bypassed.

Changed only the proof body, added the proved private helper `constant_adjunct_invImage`, and updated the node's proof text and origin to match the implementation. No statements, definitions, imports, or public interfaces changed.
