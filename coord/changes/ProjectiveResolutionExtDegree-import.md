# Sheaf.RingTheory.ProjectiveResolutionExtDegree imports

## Reason

The module compiles without the unused public import
`Mathlib.Algebra.Category.ModuleCat.Abelian`. Remove the redundant direct public import;
this changes an import interface, not any declaration signature or proof.

## Old

`public import Mathlib.Algebra.Category.ModuleCat.Abelian`

## New

The import is removed.

## Users

The three direct users import ProjectiveResolutionExtDegree with plain `import`, only
for proofs. Their public import closures therefore do not lose an exposed module through
this edge. No caller statement or proof is changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ProjectiveResolutionExtCharacterization | unclaimed | Unchanged; already publicly imports ModuleCat.Abelian directly. |
| Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees | unclaimed | Unchanged; already publicly imports ModuleCat.Abelian directly. |
| Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise | unclaimed | Uses only the unchanged theorem in its proof; no public re-export of this import. |

No forced adaptations or target statement reviews are required: no definition changed.

## Status

landed 20261014T004117-L-2840142 2026-10-14 (merge of deliver/X3/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
