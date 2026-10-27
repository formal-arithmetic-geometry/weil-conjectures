## What changed

Proved `WeilConjectures.PurCompactSupport.scalarPull_complex_normalization` from
normalized adjunction composition and uniqueness. The proof first normalizes the scalar
and geometric Hom bijections, composes them, and applies the prescribed normalization
of the restriction/direct-image comparison. It cancels only comparison isomorphisms;
no scalar computation counit is inverted.

Added two completed supporting modules:
`Sheaf.Paper.ScalarComplexAdjunctionNormalization` proves the scalar Hom normalization
on arbitrary complexes; `Sheaf.Paper.ScalarRestrictionComplexNormalization` constructs
the canonical termwise right comparison and proves its inverse complex-unit equation.
Private helpers handle the geometric normalization and the natural complex counits.
The original public theorem signature and both original public definitions are unchanged.
No other existing Lean module is changed.

Updated the item's DAG proof and dependencies and added nodes for the two supporting
statements. The completed supports were moved into separate modules after profiling
showed excessive kernel checking of the combined proof term; local auxiliary lemmas
and a general isomorphism-square cancellation lemma reduced but did not eliminate the
combined file's excess over 60 seconds. All debugging options have been removed.

Validation: `lcompile.py --all` compiled all three delivered modules successfully,
with no errors or warnings. The source signatures, original definition bodies,
node statements, dependency unions, line lengths, and zero hole counts were also checked.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.PurCompactSupport.scalarPull_complex_normalization`
(node `lem-sf-scalar-pull-coefficient-complex-normalization`).

Also proved the new supporting statements:
`WeilConjectures.PurCompactSupport.scalarComplexTranspose` and
`WeilConjectures.PurCompactSupport.scalarRestriction_complex_normalization`.

Holes closed: 1. Holes added: 0. Split off with sorry: 0.
No `sorry` remains in any delivered module. Existing obligations in imported
dependencies are unchanged.

## No longer needed

None. No original import or declared mathematical dependency was removed. All four
original proof dependencies remain used, directly or through the completed supporting
modules. There are no modules or nodes to withdraw.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The scalar adjunction's recorded unit
normalization is restricted to K-flat complexes. Applying the generic comparison
argument to arbitrary complexes needs a proved extension of that normalization.
The scalar supporting module obtains the all-complex equation from the existing
resolving-adjunction construction and identifies its adjunction with the recorded one
using the existing uniqueness clause. No flatness assumption is added.
The unit record has no separately realized steps to bypass.

## New nodes

`lem-sf-scalar-complex-adjunction-normalization`, in
`Sheaf.Paper.ScalarComplexAdjunctionNormalization`, records the proved scalar Hom
normalization on arbitrary complexes. Its private unit proof uses K-flat resolutions
only to construct and identify the adjunction, not as a hypothesis on the complex.

`lem-sf-scalar-restriction-complex-normalization`, in
`Sheaf.Paper.ScalarRestrictionComplexNormalization`, records the proved inverse
right-comparison square. Its two public definitions are actual canonical constructions
of the cochain unit and termwise restriction/direct-image isomorphism. The comparison
square is a strict part of the main normalized-adjunction argument.
No change record is required: no existing statement, definition, or interface changed.

## Second reading by W7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
