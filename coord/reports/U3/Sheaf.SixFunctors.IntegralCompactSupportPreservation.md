## What changed

Filled `AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.preservation_of_ctf_eq`
in `Sheaf.SixFunctors.IntegralCompactSupportPreservation`. Added the private proof imports
`Sheaf.Paper.CompactificationLocalizing` and `Sheaf.Paper.LocalizingClosureCtfEqualsBc`.
The statement, existing public import, and definitions are unchanged. Added two fully
proved private helpers: `image_isTriangulated` and `preservation_of_equal_generators`.
The latter checks the transport argument over an abstract coefficient before the public
theorem specializes it to O_E. Removed the original file-local projection cache-instance
registrations: using the ordinary underlying instances avoids expensive definitional
comparisons. All those local registrations were confined to this file. No public instance,
attribute, definition, or import was removed.

Updated the item's DAG proof to describe this implementation and to record the already
proved `lem-pc-right-derived-functor-triangulated` used for ambient exactness. The two
original dependencies remain used and the unit route stays intact.

For each standing scheme, its bundled separated finite-type structure gives the qcqs
instances. The over-morphism equation gives separatedness and local finite type of the
map; quasi-compactness follows from the compact source and quasi-separated target.
The quasi-compact compactification is wrapped as a boundary compactification without
altering its underlying datum. Apply `compactification_localizing` with the integral
finite-extension admissibility clause and the identity coefficient isomorphism.
Specialize `localizingClosure_ctf_equals_bc` using the same identity to transport the
localizing and coproduct clauses. Ambient triangulated composition gives the triangle
clause directly, using its existing shift comparison. Its Dctf=Dbc equality supplies finite Tor
amplitude for the input to the constructibility clause; project bounded constructibility
from its conclusion. All discrete indexing types, including the empty family, are kept.

Validation: the full module compiled cleanly through `lcompile.py` in 8.4 seconds.
Earlier specialized attempts exceeded the limit; the abstract-coefficient helper and
ordinary instance environment resolve this without changing any dependency definition,
raising the limit, disabling transparency checks, or splitting into extra modules.
All debug options and temporary proof holes are absent from the delivered Lean file.

Searches: LeanFinder returned generic homological and derived-category facts, with no
geometric preservation theorem; Loogle did not recognize the project-specific closure
name; the Mathlib grep returned no match. Direct searches in both project roots located
the two planned declarations. Their signatures and definitions were read before use.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.ProEtale.CondensedRing.IntegralCompactSupport.preservation_of_ctf_eq`
(node `lem-sfb-total-derived-preservation`). Holes closed: 1 of 1. Holes added: 0.
There are no remaining `sorry` declarations in the delivered module. No split-off
statements or other Lean modules are added. This proof uses the existing declared
proof dependencies; it does not assert that their entire dependency closure is closed.

## No longer needed

None. Both declared proof dependencies, `det-sf-comp-coherence-single` and
`det-def-localizing-closure-ctf-equals-bc`, are used. No import, node, or module is pruned.
No change to the unit route is needed.

## Where the brief, the DAG or earlier work was wrong

None. The existing proof plan can be implemented directly from its recorded declarations.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
