# HopfAlgebra.height_ker_counit_eq_ringKrullDim

## Reason

The delivery checker treats added namespace opens and section variables as an interface
change. This record documents the added proof context. Every existing declaration's
signature and visibility, and every public import, remains unchanged. Private helpers
prove translation and height preservation; there is no statement or definition repair.

## Old

The namespace previously contained only the following public theorem, with no `open`
commands or section variables:

```lean
theorem height_ker_counit_eq_ringKrullDim
    (k A : Type*) [Field k] [CommRing A] [HopfAlgebra k A]
    [Algebra.FiniteType k A] :
    ((RingHom.ker (Bialgebra.counitAlgHom k A)).height : WithBot ℕ∞) =
      ringKrullDim A := by sorry
```

## New

The theorem has exactly the same signature and a complete proof. Inside namespace
`HopfAlgebra`, private helpers use this proof context:

```lean
open Bialgebra WithConv
open scoped TensorProduct

variable {k A : Type*} [Field k] [CommRing A] [HopfAlgebra k A]
```

All added definitions and theorems are private and fully proved. The explicit `k A`
binders of the existing public theorem still supply its original universes and
hypotheses. No new instance, attribute or public notation is added. No target's meaning
changes and no target-statement review is reopened.

## Users

`tools/downstream.py Sheaf.RingTheory.HopfAlgebra.AugmentationHeight --uses
height_ker_counit_eq_ringKrullDim` reports the following textual users. Its transitive
import closure contains 337 modules, all unaffected because the public API is identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.RingTheory.HopfAlgebra.AugmentationHeight | T4 | The public theorem now has a complete proof; its type is unchanged. |
| WeilConjectures.RingTheory.HopfAlgebra.Cartier | unclaimed | Calls the same theorem with the same type; no adaptation is needed. |

## Status

landed 20261014T140637-L-118814 2026-10-14 (merge of deliver/T4/Sheaf.RingTheory.HopfAlgebra.AugmentationHeight)
