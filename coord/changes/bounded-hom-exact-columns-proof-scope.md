# CochainComplex.acyclic_homComplex_of_bounded_exact_columns

## Reason

The reduction constructs a private opposite Hom bicomplex. The preflight
classifies added scoped `open`, `section`, and `variable` commands as a visible
interface change. All existing declaration signatures and visibility are identical;
no definition used by a target changes. The new variables are scoped to Helpers
and are closed before the original theorem. `open Opposite` supplies `op` in the
private proof construction only. This record documents the syntactic change.

## Old

```lean
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex
```

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite

namespace CochainComplex

section Helpers

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {R : Sheaf J CommRingCat.{w}}
```

The section contains four proved private helper lemmas and the private concrete
bicomplex definition. It ends before the original public theorem. Every added
import is a proof import. No public signature or public definition is adapted.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.BoundedAboveFiniteFreeHomAcyclic | unclaimed | No change: the theorem signature and public imports are unchanged. |
| Sheaf.Algebra.Homology.BoundedHomExactColumns | V3 | Private proof construction and complete reduction; no signature change. |

## Status

landed 20261013T100202-L-2497602 2026-10-13 (merge of deliver/V3/Sheaf.Algebra.Homology.BoundedHomExactColumns)
