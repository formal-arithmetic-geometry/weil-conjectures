## What changed

Completed `Module.exists_annihilator_eq_of_localization_atPrime` in
`Sheaf.RingTheory.AssociatedLocalizationFg`, preserving its statement and imports.
The proof follows Stacks Project Algebra Tag 0310 (2), recorded by
`lem-sc-associated-localization-fg`: represent the localized witness as `m/s`,
clear denominators for finitely many generators of `p`, and use the product of
those denominators to obtain an element with annihilator exactly `p`.
The reverse containment uses contraction of the localized maximal ideal and
primality. No statement, definition, source-library module or public API changed.

Mathlib searches through leanfinder, loogle, the launcher grep service and local
source searches confirmed that the associated-prime descent theorem in
`Mathlib.RingTheory.Ideal.AssociatedPrime.Localization` concludes an equality
with a radical, so it cannot directly supply the required annihilator equality.
Its denominator-clearing proof supplied the finite-product template. The proof
here uses only Mathlib's existing localization, ideal span and prime ideal API.

## Proved and sorry left

Closed the one original hole:
`Module.exists_annihilator_eq_of_localization_atPrime`
(node `lem-sc-associated-localization-fg`).
No holes added, no split statements, and no sorry remains in the item module.
Single-file validation through `lcompile.py` passed cleanly in 2.6 seconds.

The finite product also covers the empty generating set (`p = 0`): its value is
one and the reverse-containment argument still applies. No Noetherian or finite
module hypothesis is introduced. The zero module cannot satisfy the premise
because its element annihilator is the whole localized ring, whereas the
localized maximal ideal is proper.

## No longer needed

None. No imports removed or added; both recorded definition dependencies,
`def-weil-pbc-localization-at-prime` and `def-weil-pbc-module-localization`, are
used. No modules or nodes are withdrawn. The existing DAG proof remains the
same denominator-clearing argument, with the initial containment used directly
in the final reverse-containment calculation rather than named separately.
The auxiliary observation that the resulting element is nonzero is unnecessary
as a separate step: it follows from the proved annihilator equality and the
properness of `p`.

## Where the brief, the DAG or earlier work was wrong

No mathematical corrections required. The existing warning that Mathlib's
associated-prime theorem uses radicals is correct. The proof can combine the
initial contraction calculation with the final reverse-containment step without
changing the argument or its dependencies.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
