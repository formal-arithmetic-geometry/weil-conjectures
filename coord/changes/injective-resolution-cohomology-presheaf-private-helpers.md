# CategoryTheory.Sheaf.injectiveResolution_cohomologyPresheaf_data

## Reason

The stage-3 interface-command check detects the namespace, universe, open, and variable
commands accompanying proved private helpers. This record documents those command additions.
No existing public signature, definition, visibility, instance, or attribute changes.
All new declarations are private. The added imports are proof-only.

## Old

```lean
@[expose] public section
universe u v
namespace CategoryTheory
```

The only public theorem is
`CategoryTheory.Sheaf.injectiveResolution_cohomologyPresheaf_data`; its original complete
signature is retained verbatim in the delivered module.

## New

```lean
@[expose] public section
universe u v w

namespace CategoryTheory.InjectiveResolution
open Opposite Abelian
variable {A : Type u} [Category.{v} A] [Abelian A]
  {F : A} (I : InjectiveResolution F)
open CochainComplex HomComplex
```

This namespace is closed after the generic private helpers. The original namespace then
opens with `open Opposite Abelian` for the private sheaf-section comparison helpers.
The extra universe `w` is used only by private generic Ext comparisons. Existing theorem
universe parameters and binders are unchanged. Scoped transparency options affect helper
proof elaboration only; no global options or exported instances are added.

## Users

`tools/downstream.py --uses CategoryTheory.Sheaf.injectiveResolution_cohomologyPresheaf_data`
lists the following two actual users (including the declaration's own module):

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.InjectiveResolutionCohomologyPresheafData | K1 | The proof is closed; public signature identical. |
| Sheaf.CategoryTheory.InjectiveResolutionCohomologyPresheaf | unclaimed | Its application of the public theorem has identical type and visibility; no adaptation. |

All 174 transitive importers retain the same public interface. No target definition or
statement changes, so no target statement review is reopened. No forced adaptations occur.

## Status

landed 20261012T194120-L-458016 2026-10-12 (merge of deliver/K1/Sheaf.CategoryTheory.InjectiveResolutionCohomologyPresheafData)
