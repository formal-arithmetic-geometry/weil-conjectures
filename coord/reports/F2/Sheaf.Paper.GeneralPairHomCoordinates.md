## What changed

Proved `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.pairHomCoordinates`
with its full ten-clause statement unchanged. Reused the existing proved intrinsic
transport, coordinate, bilinearity, additive-inclusion and representative APIs.
Proved same-stage addition and zero by injectivity of the actual `homCoordinates`,
its transferred additive equivalence, representative normalization and the additive
structure maps of the direct limit. Applied `Functor.map_isZero` to the bottom-stage
inclusion; its image is definitionally the requested literal pair.

Updated the item's proof steps and proof origin to identify these existing proofs.
No shared definition, instance, declaration signature or target changes.
The original local opacity annotation on homAddCommGroup is omitted so the
transferred additive equivalence can be used; no exported attribute changes.

Validation: the final module compiled cleanly through lcompile.py in 4.9 seconds,
with no warnings or errors. The theorem's source signature is byte-for-byte
unchanged. The delivered Lean file contains no sorry or forbidden declarations;
all lines are at most 100 characters. Only proof and proof_origin changed in the
node, and proof_deps still equals the union of its proof-step uses.

Searches through `msearch.py` used LeanFinder (directed pair-category morphisms and
additive colimit representatives), Loogle (`Equiv.addEquiv`) and grep
(`linearEquiv_of|map_add|iff_id_eq_zero`). The useful generic match is
`Equiv.addEquiv`; library searches found the concrete already-proved public APIs.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.pairHomCoordinates`
(node `lem-pur-general-pair-hom-coordinates`). No holes added or split off.
No `sorry` remains in the delivered module. Existing imported obligations are
unchanged; this is a proof from the existing declarations, not a claim that all
imported mathematics is now axiom-free.

## No longer needed

Remove the unused import `Sheaf.CategoryTheory.ExactStagePairData`; the theorem
uses the actual pair construction already provided by the retained coefficient
module, without forming an `ExactStagePairData` value. There are no current Lean
direct importers of the assigned module. No declaration or module is withdrawn.
The existing DAG dependencies remain: their scalar-stage, rationalization,
compositum, pair-quotient and direct-limit constructions support the public APIs
used here. No unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

Most of the planned argument is already proved in
`GeneralAlgebraicallyClosedCoefficients`: transportSystem,
homCoordinates_existsUnique, composition_bilinear, inclusion_additive and
representatives. Its same-stage addition/zero helpers are private, so those two
short arguments are proved here using the public coordinate normalization.
The new assertion for every bottom-stage zero object follows directly from the
existing additive inclusion. No statement repair is required.

Import change record: `coord/changes/F2-pair-hom-coordinate-import.md`.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
