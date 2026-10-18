## What changed

Proved all three open theorems of `Sheaf.Paper.FieldCohomologyScalarExtension`
without changing any existing signature, definition, visibility or public import.
Added the proof-only import `Mathlib.RingTheory.TensorProduct.Finite`.

The unique derived homology comparison is obtained as the preimage of the
complex comparison under fully faithful precomposition with Q. Its prescribed
components and uniqueness follow from map_preimage and localization extensionality.
Three proved private helpers record those components, composition of short-complex
homology comparisons, and the complex scalar-tower equality. The derived tower
proof forms two natural isomorphisms, checks them on Q A, uses naturality along
the scalar-extension factorization, and reduces to the complex identity.
Finite-dimensionality is transported along the complex comparison after finite
base change; quasi-isomorphism preservation is Mathlib's exact-functor instance.

Updated the existing node's proof and proof dependencies to record localization
and the normalized derived tower used by the implementation. The unit's route
is unchanged. Single-file remote compilation passes without warnings.

## Proved and sorry left

Closed 3 of 3 original holes, all attached to
`lem-weil-cohomology-commutes-scalar-extension`:

- `DerivedCategory.existsUnique_fieldDerivedHomologyIso`.
- `DerivedCategory.fieldDerivedHomologyIso_tower`.
- `DerivedCategory.fieldComplexScalarExtension_properties`.

Holes added: 0. Sorries left in the delivered module: 0. No split-offs.
The tower proof uses the existing
`DerivedCategory.existsUnique_fieldScalarTower` in
`Sheaf.Paper.FieldDerivedScalarTower`, which remains an imported obligation.
This delivery does not claim that all transitive axioms are eliminated.

## No longer needed

None. Both original public imports remain necessary. All four original declared
proof dependencies are used through their Mathlib declarations or existing
field-exactness instances. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the localization argument for the module's
uniquely normalized derived comparison, and did not list the existing normalized
derived scalar tower that its derived tower statement uses. The updated proof
records both existing dependencies explicitly. There is no mathematical statement
repair and no change record is needed.

The complex tower square needs no new cycle-representative theory: the existing
short-complex homology comparison's universal-property API and naturality give it.
The edge cases (zero complexes, identity field maps, unbounded complexes, and
infinite-dimensional terms with finite-dimensional cohomology) require no extra
hypotheses; the proof uses exactness in three degrees and degreewise finiteness.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
