## What changed

Proved the two auxiliary theorems in
`Sheaf.Paper.SiteLocallyConstantFiniteType`. Each constructs the local-property
instance using Mathlib's corresponding covering-sieve theorem for the
commutative-ring sheafification unit. The equalizer sieve and image sieve are
definitionally unchanged by `forget₂ CommRingCat RingCat`. No declaration
signature, definition, instance attribute, or import changed.

Validation: the complete module compiled through `lcompile.py` without errors
or warnings (3.4 seconds). LeanFinder and source searches located Mathlib's
`Presheaf.isLocallyInjective_toSheafify'` and
`Presheaf.isLocallySurjective_toSheafify'`; the proofs use
`Presheaf.equalizerSieve_mem` and `Presheaf.imageSieve_mem` with those existing
instances. This works for arbitrary sites, including empty covers, and the zero
coefficient ring: no nonemptiness, nontriviality, or enough-points hypothesis is
introduced.

## Proved and sorry left

Closed 2 of 2 original holes, both attached to
`def-weil-pbc-site-locally-constant-finite-type`:

- `SheafOfModules.constantCommRingUnit_locallyInjective`.
- `SheafOfModules.constantCommRingUnit_locallySurjective`.

No `sorry` remains in the module. No holes were added or split off.
`SheafOfModules.IsLocallyConstantFiniteType` remains its original real definition.

## No longer needed

None. Both original public imports remain necessary for the definition:
`Sheaf.Paper.StrictPerfectCoefficientPackage` supplies the constant module
presheaf and module sheafification setup, and
`Mathlib.RingTheory.Finiteness.Defs` supplies `Module.Finite`.
The node has no stated proof dependencies or proof steps to prune. No nodes or
modules are bypassed, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

None. The two elementary preservation assertions can be proved directly from
Mathlib by reusing the same covering sieves; no additional infrastructure or
statement repair is needed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
