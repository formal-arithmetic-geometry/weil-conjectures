## What changed

Completed `CategoryTheory.algebraSheafQuotient_cokernel` in
`Sheaf.CategoryTheory.AlgebraSheafQuotientCokernel`, preserving its statement and all
three public definitions verbatim. All added helpers are private and fully proved.

The sectionwise quotient is regarded as an O-module presheaf. Its sheafification
unit is locally bijective. A module map annihilating the ideal factors sectionwise
by `QuotientAddGroup.lift`; naturality and linearity are checked on quotient
representatives. Mathlib's `PresheafOfModules.homEquivOfIsLocallyBijective` then gives
the unique module-sheaf factorization. Comparing this cokernel cofork with the
chosen cokernel proves the normalized isomorphism. The other clauses use local
surjectivity of the quotient projection and sheafification unit, and
`Ideal.Quotient.lift` followed by `sheafifyLift` for algebra factorization.

Updated the existing node's proof, proof dependencies, and proof origin to record
this implementation. No public signatures, public imports, definitions, or
consumer modules changed. The local instances are introduced inside a private proof.

Validation: the complete proof compiled successfully through `lcompile.py`
in 11.9 seconds, with no errors or warnings. The final import-pruned version is
checked again by the delivery compilation and axiom probes.

## Proved and sorry left

Closed 1 existing hole: `CategoryTheory.algebraSheafQuotient_cokernel`
(node `lem-weil-pbc-ringed-space-algebra-quotient-cokernel`). All three conjuncts
are proved. Zero holes remain in the item; zero holes were added, and zero
statements were split off. This is a proof, not a decomposition.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal` and removed
`lem-weil-pbc-site-sheafification-sections-local` from this node's proof dependencies.
Mathlib's locally bijective module descent proves precisely the needed gluing,
uniqueness, and linearity. The separate proof-plan calculation
`ker(q_U) = I(U)` is unnecessary for the cokernel universal property. The existing
local-sections declaration and module remain available for other consumers.

No other nodes or modules are withdrawn. Existing public imports remain part of
the module's public interface. The unit statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing proof plan is valid but longer than
necessary: its explicit transfer of local representatives, kernel computation,
and gluing are handled by the existing Mathlib descent API. This works on every
open, including the empty open, since the API uses the full sheaf condition.
The zero ideal, whole ideal, and empty space require no additional assumptions.

Searches were run with `msearch.py` (LeanFinder, Loogle, and grep) and direct
source searches. Loogle located the module descent equivalence; its full
signature and proof were read in Mathlib. Sources read: Stacks Modules, the
cokernel construction before Tag 01AG and Tag 01AH; Sheaves Tags 0087 and 0089.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
