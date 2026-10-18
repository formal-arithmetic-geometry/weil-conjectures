## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Etale.etaleStalkSpecialization_naturality`, in
`Sheaf.AlgebraicGeometry.SpecializationCospecializationArrows`, by the proof described
in its existing docstring. No signature, definition, docstring, import, or node was changed.

First restrict the stalk colimit to the initial small category of affine pointed
neighbourhoods. The characterizing equations of
`existsUnique_strictHenselizationStalkRestriction` reduce naturality of the chosen
restriction maps to naturality of the adjunction unit, presheaf restriction, and the
inverse global-sections comparison. Then compose the restriction with the natural
transformation formed from `globalGerm` and `upperStarCompSheafFiberIso`.

The representative-section calculation also appears in the proved
`strictHenselizationSectionRestriction_naturality` in
`Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm`. Here it is a local calculation
using the current imports, avoiding that module's unrelated higher-cohomology machinery.

The proof applies to every stated morphism of sheaves and every geometric point `t`;
it adds no algebraicity, properness, acyclicity, or torsion hypothesis. It uses the
existing uniquely characterized restriction, and introduces no arbitrary chosen data.

Validation: the complete proof compiled through `lcompile.py` within the 60-second
file limit. The final module passed the delivery dry run's compilation, signature,
axiom, and report checks with review class `AUTO`.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.etaleStalkSpecialization_naturality`
(node `def-weil-pbc-specialization-cospecialization-arrows`).

Added 0 holes. Split off 0 statements. There are no `sorry` declarations left in
the delivered module. Previously imported dependencies retain their existing proofs;
this delivery does not claim to close their holes.

## No longer needed

None. No imports were added or removed. All six existing public imports supply
statements or definitions of the canonical arrows that remain in this module.
The existing proof route and the unit's realized statements and steps are retained;
no node or module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface defect was found. The item's node has an empty `proof`
array because it records the arrow definitions; the existing naturality docstring
provides the proof, which is now implemented without new dependencies or nodes.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
