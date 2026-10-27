## What changed

Proved `WeilConjectures.integralOpenTensorModuleQuotientSquare` by transposing with the
ordinary scalar adjunction and testing on open-extension generators. The proved private helpers `quotient_sections`, `native_unit_heq`,
`quotient_native_unit`, and `quotient_unit_section` specialize the already proved
quotient mate/unit laws, using the existing `nativeUnit_eq` bridge. The calculation
is generic over ring sheaves and adjunctions before specialization, preventing the
kernel from unfolding the completed coefficient data. The private helpers
`unit_map_section`, `section_apply_heq`, and `scalar_open_generator_ext` handle the
underlying sections and the two adjunction extensionality laws.
The proof then uses `TensorComparison.generators`, finite-extension naturality on
sections, and the supplied `hgen`. All existing signatures and public imports are
preserved. The four added proof imports expose the already proved private helper
APIs in `OpenScalarTransitionCompatibility`, `OpenSystemUnitSections`, and
`CoefficientExtensionAssociationQuotientUnits`, and
`CoefficientExtensionOrdinaryStrictTensor`. The item's node records their use.

Validation: the complete file compiled in 9.0 seconds. The profiling options used
to locate the expensive concrete mate conversion have been removed for delivery.
The original theorem signature and public imports are byte-for-byte preserved.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.integralOpenTensorModuleQuotientSquare`
(`lem-sf-integral-open-tensor-module-quotient-square`).
No holes added or split off; no `sorry` remains in this delivery.
All seven private helpers are proved in full.

## No longer needed

No existing imports removed. The planned direct dependency
`lem-cbc-ringed-open-scalar-adjunction`
(`Sheaf.CategoryTheory.RingedOpenScalarAdjunction`) is unnecessary for this proof:
the generator-normalized comparison is already supplied as a hypothesis, and equality
of the two maps follows from the existing open-extension extensionality helper.
No assertion is made that other consumers cease to need that node or module.
The ordinary coefficient calculus and tensor-comparison generator normalization remain
needed. No module is withdrawn and no unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original two-step plan was sufficient. The missing glue was already proved in
support modules for strict tensor transitions: quotient-unit sections, extension
extensionality, and naturality of finite extension on generators. Reusing those
helpers closes this obligation without another split. The proof uses only ordinary
module adjunctions; it introduces no flatness, completeness, or boundedness assumptions.

## Second reading by W6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
