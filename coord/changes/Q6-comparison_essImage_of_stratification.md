# comparison_essImage_of_stratification

## Reason

The assigned classicality theorem allows infinite Noetherian coefficient rings.
This support theorem unnecessarily required finite coefficients. Its existing argument
works for arbitrary commutative rings. No definition or target statement changes.
The modified support module is unclaimed. No adaptation of another held module is made.

## Old

```lean
theorem comparison_essImage_of_stratification
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X : Scheme.{u}}
    (S : Scheme.Stratification X)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k : Fin S.n, (ν^*(S.domain k)[ModuleCat.{u + 1} Λ]).essImage
      (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F
```

## New

```lean
theorem comparison_essImage_of_stratification
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    (S : Scheme.Stratification X)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hS : ∀ k : Fin S.n, (ν^*(S.domain k)[ModuleCat.{u + 1} Λ]).essImage
      (((S.immersion k)^*[ModuleCat.{u + 1} Λ]).obj F)) :
    (ν^*(X)[ModuleCat.{u + 1} Λ]).essImage F
```

## Users

The table lists direct declaration users from
`tools/downstream.py Sheaf.Paper.ProEtaleStratifiedEssentialImage --uses comparison_essImage_of_stratification`.
Every downstream statement stays identical. Direct consumers keep their proofs;
the changed theorem is strictly more general and retains their specializations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical | Q6 | Statement unchanged; removing a hypothesis preserves its finite-ring use. |
| Sheaf.Paper.ProEtaleStratifiedCounit | unclaimed | Statement unchanged; removing a hypothesis preserves its finite-ring use. |
| Sheaf.Paper.ProEtaleStratifiedEssentialImage | unclaimed | Generalized here; proof retained. |

## Status

landed 20261019T005405-L-2762980 2026-10-19 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.ConstructibleProEtaleClassical)
