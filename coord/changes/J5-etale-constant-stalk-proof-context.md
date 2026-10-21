# AlgebraicGeometry.Scheme.etale_stalk_constant_complex_retraction proof context

## Reason

Complete all six theorem proofs using the existing general constant-realization exactness,
constant-scalar equivalence, point fibres and module sheafification units. Private proved
helpers need explicit universe restrictions of existing module limit and filtered-colimit
instances. They are registered only locally. All existing public declarations, definitions,
attributes and signatures remain verbatim. The unused public import
`Mathlib.Algebra.Homology.DerivedCategory.Basic` is removed; the other public imports
provide all complex and homology declarations in the signatures. No target meaning changes.

## Old

The file has the original standing variables:

```lean
variable (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A]
variable {T} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
```

It has no private helper registrations and the six theorem proofs are `by sorry`.
It publicly imports `Mathlib.Algebra.Homology.DerivedCategory.Basic`.

## New

The redundant public derived-category import is removed; no statement or definition
in this module uses derived categories. The original variable commands remain. A `variable (T)` command before private helpers
makes their scheme argument explicit, followed by `variable {T}` before the last public
theorem, restoring its original signature. Private proved theorems are registered by
`attribute [local instance]`:

- `moduleLimitsSmall`: existing module limits at the smaller point universe;
- `moduleAB5Small`: restriction of the existing AB5 instance;
- `moduleForgetFilteredSmall`: restriction of filtered-colimit preservation;
- `moduleSheafFiberAdditive`: additivity from finite-limit preservation;
- `constantModuleUnit_locallyInjective` and `constantModuleUnit_locallySurjective`:
  local bijectivity of the actual module-sheafification unit;
- `regularModuleUnit_locallyInjective` and `regularModuleUnit_locallySurjective`:
  local bijectivity of the ring-sheafification unit viewed as a module map.

Each registration is local to the existing namespace. They introduce no new global
instances or alternative data constructions. Declaration-scoped transparency options
only elaborate these private helper proofs; no file-level option changes. The last
public theorem is proved by a natural module isomorphism lifted termwise and the same
constant-section construction for the regular module. There are no additional public
statements or definitions.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.EtaleStalkConstantComplexExactness`
reports zero current Lean downstream modules. DAG parents still need the item,
including `lem-sfb-etale-derived-tensor-stalk`, whose interface is unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.EtaleStalkConstantComplexExactness | J5 | Six complete proofs; public interface unchanged. |

## Status

landed 20261021T111219-L-58712 2026-10-21 (merge of deliver/J5/Sheaf.SixFunctors.EtaleStalkConstantComplexExactness)
