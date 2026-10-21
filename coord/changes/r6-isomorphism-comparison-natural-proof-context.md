# Sheaf.Paper.IsomorphismComparisonNatural elaboration commands

## Reason

The completed proofs use Mathlib's functor-whiskering names, the scoped zero-object
notation, and the scheme-category notation. Local irreducibility keeps elaboration
of the integral comparison within the single-file compile limit by avoiding
unnecessary unfolding of the coefficient ring, constant sheaf, and standard derived
category. Server preflight requests this record for the changed commands.

These are elaboration-context changes in the item held by R6. Both original public
theorem signatures and all public imports are preserved; no definition or instance
body changes. All new helper declarations are private and proved.

## Old

The corresponding original context was:

```lean
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ZeroObject
open AlgebraicGeometry.Scheme
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace WeilConjectures

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  constantSheaf HasDerivedCategory.standard
```

The pre-existing sheafification-instance attribute and all pre-existing options
remain unchanged. The new irreducibility attributes are explicitly local.

## Users

`tools/downstream.py Sheaf.Paper.IsomorphismComparisonNatural --uses
inverseImagePullbackComparisonFinite_natural inverseImagePullbackComparisonIntegral_natural`
reports zero downstream modules and only the item's own occurrence of each theorem.
No dependent module requires adaptation, and no target statement or definition
changes. The unchanged DAG parents may use these same theorem statements when their
proofs are completed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismComparisonNatural | R6 | Two existing theorem proofs filled; local proof context extended; statements unchanged. |

## Status

landed 20261021T130133-L-2553582 2026-10-21 (merge of deliver/R6/Sheaf.Paper.IsomorphismComparisonNatural)

The final item module compiled cleanly through `lcompile.py` in 20.2 seconds. The
maintainer's global build and independent review remain pending.
