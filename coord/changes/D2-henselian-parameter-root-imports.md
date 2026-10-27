# Algebra.henselian_parameter_root_regularity

## Reason

Prove the full theorem by direct monomial normal forms and explicit quotient maps.
The statement uses ring regularity and local residue fields. It does not use scheme
regularity or scheme residue fields. Remove the two unused public imports from
Sheaf.RingTheory.HenselianParameterRootRegularity. All existing declaration signatures,
visibility, universes and the coordinate definition remain verbatim.

## Old

```lean
public import Mathlib.AlgebraicGeometry.ResidueField
public import Sheaf.AlgebraicGeometry.IsRegularScheme
```

## New

Both unused import lines are removed. The retained imports already provide
IsRegularLocalRing and IsLocalRing.ResidueField, including the required R-algebra
structure. No declaration is removed or restated.

## Users

`tools/downstream.py Sheaf.RingTheory.HenselianParameterRootRegularity --uses
Algebra.henselian_parameter_root_regularity` reports zero downstream modules and only
this module as a declaration use. An independent scan of all tracked-library Lean
sources finds no direct importer of this module. Its DAG parents remain intact: this
is a proof delivery, not a withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.HenselianParameterRootRegularity | D2 | Complete proof; unchanged public declarations; removes unused scheme imports. |

No consumer adaptations are needed, and no target statement or definition changes.

## Status

landed 20261023T123423-L-1186083 2026-10-23 (merge of deliver/D2/Sheaf.RingTheory.HenselianParameterRootRegularity)
