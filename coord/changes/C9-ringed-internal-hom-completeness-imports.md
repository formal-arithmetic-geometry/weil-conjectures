# CategoryTheory.isLocallyDerivedRingedIdealComplete_derivedInternalHom

## Reason

Prune the unused public import of the telescope localization module while
proving local derived completeness by closed tensor-Hom adjunction and
symmetry. Every existing declaration and its signature/visibility is retained.
Only the publicly reexported import list changes; no definition changes.

## Old

```lean
public import Sheaf.CategoryTheory.RingedSiteLocalization
```

## New

The unused import above is removed. All other public imports are retained.
The new proof dependencies are ordinary, non-public imports:

```lean
import Mathlib.CategoryTheory.HomCongr
import Sheaf.Algebra.Homology.RingedInternalHomExactRestriction
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
```

## Users

`tools/downstream.py ... --uses isLocallyDerivedRingedIdealComplete_derivedInternalHom`
found no external textual user of the theorem (only its own declaration).
The import graph has two direct importers, both checked individually against
the changed module by lcompile.py in a sandbox overlay. Neither is adapted.
Transitive importers retain the same theorem and definitions; the static
import-pruning gate checks their declaration access.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete | C9 | Proof completed; unused public import removed. |
| Sheaf.Paper.CompletedProjectionCoherence | T4 (not adapted) | No signature or proof change; direct consumer compilation checked. |
| Sheaf.Paper.RationalThickEvaluation | unclaimed (not adapted) | No signature or proof change; direct consumer compilation checked. |

## Status

landed 20261019T093320-L-2294461 2026-10-19 (merge of deliver/C9/Sheaf.Algebra.Homology.RingedInternalHomDerivedComplete)
