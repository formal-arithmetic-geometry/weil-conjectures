# DerivedCategory.rlim_perfect_complete

## Reason

The proof uses ordinary module tensor comparisons and the proved source K-flat tensor
model. The former public change-of-rings import is unnecessary for every statement and
definition of this module. Removing it keeps a proof dependency from being exported.
No declaration signature or definition body changes.

## Old

```lean
public import Sheaf.Algebra.Homology.DerivedChangeOfRings
```

## New

The import is removed. The proof imports
`WeilConjectures.CategoryTheory.DerivedCategory.FlatModel` and
`Sheaf.Algebra.Homology.TensorRestrictExtendScalarsModule` without `public`.

## Users

`python3 tools/downstream.py Sheaf.RingTheory.RlimPerfectComplete` reports zero downstream
modules on 2026-10-18. All original public declaration signatures and bodies of definitions
are unchanged. No consumer adaptation is required, and no target statement changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.RlimPerfectComplete | C2 | Removes an unused public import; proves its theorem. |

## Status

landed 20261018T101336-L-3972165 2026-10-18 (merge of deliver/C2/Sheaf.RingTheory.RlimPerfectComplete)
