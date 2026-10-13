# affineOpenSections_zero_detection imports

## Reason

Remove a redundant public proof import from Sheaf.Paper.AffineOpenSectionsZeroDetection.
`IsAffine` and `IsOpenImmersion` in its unchanged signature are already supplied by
its public étale-site import. `AffineTransitionLimit`, privately imported for the
proof, supplies the affine-transition API. All statements and definitions keep their
text and meaning. The delivery also adds the local helper's public declaration in its
own new module; it changes no existing declaration.

## Old

```lean
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
```

## New

```lean
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import Sheaf.Paper.EtaleSectionZeroNeighbourhood
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
```

## Users

`tools/downstream.py Sheaf.Paper.AffineOpenSectionsZeroDetection --uses
 affineOpenSections_zero_detection` lists 169 transitive importers, but only the
core below and the item itself mention the declaration. The single direct importer
imports Morphisms.Affine publicly itself. Thus it shields all transitive importers
from the reexport removal: their available affine API is unchanged. No adaptation
is needed. No target statement or used definition changes; target review is not
reopened.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AffineOpenSectionsZeroDetection | P1 | Signature unchanged; compiled cleanly with reduced imports. Uses the new helper only in its proof. |
| Sheaf.Paper.AffineOpenSectionsCanonicalColimitCore | unclaimed | Its own public Morphisms.Affine import supplies the removed reexport. Its invocation of affineOpenSections_zero_detection and its statement are unchanged. |

Attempted single-file compilation of an unchanged scratch copy of the direct
importer against the sandbox overlay. It stopped before elaboration because the
shared compiled library lacks Sheaf.Paper.AffineOpenSectionsDescent. This is a
missing baseline dependency, not a compiler failure caused by the import change.
Source inspection establishes that its own public affine import remains; the
maintainer's global build verifies the delivery after landing.

## Status

landed 20261013T100046-L-2474238 2026-10-13 (merge of deliver/P1/Sheaf.Paper.AffineOpenSectionsZeroDetection)
