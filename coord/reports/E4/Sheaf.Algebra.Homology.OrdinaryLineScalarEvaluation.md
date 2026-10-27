## What changed

Proved `SheafOfModules.OrdinaryLineScalar.ordinary_scalar_line_evaluation` with its
statement and public imports unchanged. Added only proved private helpers and proof
imports in the item module. The ordinary proof precomposes with inverse evaluation,
checks unit sections on a trivializing cover using transported signed bases, and glues
by sheaf separatedness. A categorical calculation transports this square through the
fixed representative comparisons. Faithful restriction to flat models gives equality
on all derived objects. Updated the item's node to describe this proof.

## Proved and sorry left

Closed the one original hole:
`SheafOfModules.OrdinaryLineScalar.ordinary_scalar_line_evaluation`
(node `lem-pur-ordinary-line-scalar-evaluation`). No holes added or split off.
No `sorry` remains in the delivered module. All added helpers are private and proved.
The complete module compiled without warnings in 37.9 seconds using `lcompile.py`.
A text comparison confirms the public theorem signature is unchanged.

## No longer needed

No existing imports removed and no modules withdrawn. The proof uses the existing
flat-descent module's faithful restriction and computation-isomorphism lemmas instead
of repeating resolution, K-flat pullback, and localization constructions in this file.
The original direct proof dependencies `lem-pc-kflat-resolution`,
`lem-weil-pbc-ringed-topos-kflat-pullback`,
`lem-pc-sites-sheaf-tensor-bilinear-universal`, and
`lem-weil-pbc-localization-universal-property` are replaced by the more specific proved
APIs listed in the updated node. They can remain needed transitively elsewhere;
this delivery claims no withdrawal of those modules or changes to the unit route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The planned argument is valid. Precomposing
with inverse cancellation shortens its local verification: only the opposite signed
basis vectors need to be evaluated, avoiding a fresh bilinearity calculation for
arbitrary multiples. The scalar computation is invertible for an arbitrary supplied
presentation by its universal property, via the existing proved adjunction API.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
