# WeilConjectures.PurityVanishingAtComponent

## Reason

The proof-only module retains the exact public proposition while replacing proposition
instance binders with ordinary `let` binders. Lean's proposition-instance linter requires
this form and the elaborated proposition is unchanged. The change is local to the item
module and has no mathematical effect.

## Old

```lean
  ∃ (Ω : Type u) (hΩ : Field Ω) (hΩalg : @IsAlgClosed Ω hΩ),
    letI := hΩ
    letI := hΩalg
    ∃ (y : Spec (.of Ω) ⟶ T),
      Set.range (((Scheme.Hom.toLRSHom' y).base : TopCat.Hom _ _).hom) ⊆
          connectedComponent x ∧
        purityProEtaleStalkMap P T y f = 0
```

## New

```lean
  ∃ (Ω : Type u) (hΩ : Field Ω) (hΩalg : @IsAlgClosed Ω hΩ),
    let := hΩ
    let := hΩalg
    ∃ (y : Spec (.of Ω) ⟶ T),
      Set.range (((Scheme.Hom.toLRSHom' y).base : TopCat.Hom _ _).hom) ⊆
          connectedComponent x ∧
        purityProEtaleStalkMap P T y f = 0
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PurLisseMorphismRigidity | F5 | Defines and proves the proposition; proof uses the unchanged elaborated type. |

## Status

landed 20261020T131957-L-1397595 2026-10-20 (merge of deliver/F5/Sheaf.Paper.PurLisseMorphismRigidity)
