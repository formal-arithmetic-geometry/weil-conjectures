## What changed

Proved both local-bijectivity properties of the constant coefficient unit in
`lean/Sheaf/CategoryTheory/ConstantCoefficientScalarExtension.lean`. Each proof constructs
its typeclass using the covering-sieve property of the original commutative-ring
sheafification unit. The underlying section maps, equalizer sieves and image sieves are
definitionally unchanged by `forget₂ CommRingCat RingCat`.

The shorter-route searches used LeanFinder (sheafification units and local bijectivity),
Loogle (`CategoryTheory.Presheaf.IsLocallyInjective, CategoryTheory.toSheafify`), and grep
(`isLocally(Injective|Surjective)_toSheafify`), together with searches of both library roots.
They found Mathlib's `Presheaf.isLocallyInjective_toSheafify'` and
`Presheaf.isLocallySurjective_toSheafify'`. The proofs use their consequences
`Presheaf.equalizerSieve_mem` and `Presheaf.imageSieve_mem`.

All declaration signatures, definitions, visibility, attributes and imports are unchanged.
The assigned module compiled without warnings through `lcompile.py`.

## Proved and sorry left

Closed 2 of 2 original holes:

- `SheafOfModules.constantCoefficientUnit_isLocallyInjective`.
- `SheafOfModules.constantCoefficientUnit_isLocallySurjective`.

Both belong to `def-weil-pbc-constant-coefficient-scalar-extension`. No `sorry` remains
in the item; no holes, modules or nodes were added. These are complete proofs, with no
new decomposition.

## No longer needed

None. Both existing public imports are needed by the definitions:
`Sheaf.Algebra.Homology.DerivedChangeOfRings` supplies derived scalar extension, and
`Sheaf.Paper.StrictPerfectCoefficientPackage` supplies the constant module presheaf.
The node has no proof dependencies to prune. No blueprint unit statement or step was
bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The node is a definition node with an empty proof plan; its two supporting theorem
holes follow directly from existing Mathlib sheafification instances, as their docstrings
suggest. No statement or definition repair was necessary.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
