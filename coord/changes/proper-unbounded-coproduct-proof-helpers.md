# Proper unbounded coproduct proof helpers

## Reason

Complete both coefficient cases along the existing six-step unit route. Two proved
helper declarations expose the categorical window transport and preservation of
coproducts by double good truncation. The item also sets three elaboration options
used by its proofs. No existing declaration signature, definition, visibility,
instance or target statement changes. All new imports of the item are proof imports.

## Old

The two helper modules and their declarations were absent. In the item, the option
block was exactly:

```lean
set_option autoImplicit false
```

## New

The item's option block is exactly:

```lean
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The new public helper signatures, verbatim, are:

```lean
theorem derivedTruncation_coproducts
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) (I : Type (u + 1))
    (K : I → DerivedCategory (pulledBackModuleObjects Λ X)) (c : Cofan K)
    (hc : IsColimit c) (q r : ℤ) :
    Nonempty (IsColimit (((DerivedCategory.TStructure.t.truncLE q) ⋙
      DerivedCategory.TStructure.t.truncGE r).mapCocone c))
```

```lean
theorem properUnbounded_coproductComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    {X Y : Scheme.{u}} (p : X ⟶ Y) (d : ℤ)
    (hwindow : ProperUnboundedWindowAssertions Λ p d)
    (hsumX : ∀ (I : Type (u + 1)) (K : I → DerivedCategory (pulledBackModuleObjects Λ X))
      (c : Cofan K), IsColimit c →
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt))
    (hsumY : ∀ (I : Type (u + 1)) (K : I → DerivedCategory (pulledBackModuleObjects Λ Y))
      (c : Cofan K), IsColimit c →
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt))
    (htrunc : ∀ (K : DerivedCategory (pulledBackModuleObjects Λ X)) (n : ℤ),
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj K)) →
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncLE n).obj K))) ∧
      (∀ m, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ m).obj
          ((DerivedCategory.TStructure.t.truncGE n).obj K))))
    (hH : ∀ (I : Type (u + 1))
      (K : Discrete I ⥤ DerivedCategory (pulledBackModuleObjects Λ Y)) (c : Cocone K),
      IsColimit c → ∀ q : ℤ,
        Nonempty (IsColimit ((DerivedCategory.homologyFunctor _ q).mapCocone c)))
    (hT : ∀ (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)) (c : Cofan K),
      IsColimit c → ∀ q r : ℤ,
      Nonempty (IsColimit (((DerivedCategory.TStructure.t.truncLE q) ⋙
        DerivedCategory.TStructure.t.truncGE r).mapCocone c)))
    (hbounded : ∀ (a b : ℤ) (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)),
      (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      (∀ i n, n < a ∨ b < n → IsZero ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
      ∃ (c : Cofan K) (_ : IsColimit c),
        Nonempty (IsColimit ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.mapCocone c))) :
    ∀ (I : Type (u + 1))
      (K : I → DerivedCategory (pulledBackModuleObjects Λ X)),
    (∀ i n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
      ((DerivedCategory.homologyFunctor _ n).obj (K i))) →
    ∃ (c : Cofan K) (_ : IsColimit c)
      (c' : Cofan (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj (K i)))
      (hc' : IsColimit c'),
      (∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ X)
        ((DerivedCategory.homologyFunctor _ n).obj c.pt)) ∧
      (∀ n, ObjectProperty.ind.{u + 1} (IsConstantModelConstructible Λ Y)
        ((DerivedCategory.homologyFunctor _ n).obj c'.pt)) ∧
      IsIso (hc'.desc (Cofan.mk
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj c.pt)
        (fun i ↦ (CondensedRing.lowerStar Λ p).rightDerivedFunctor.map (c.inj i))))
```

## Users

`tools/downstream.py Sheaf.Paper.ProperUnboundedCoproducts --uses
properUnbounded_preservesCoproducts properUnbounded_preservesCoproducts_padicAlgCl
ProperUnboundedCoproductAssertions` found 218 transitive importers and no textual
uses of the three existing declarations outside their defining module. There is
one direct importer. The added elaboration options do not change any declaration
or persist into importing modules. No consumer needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ProperUnboundedCoproducts | U2 | two proof holes closed; uses both new helpers |
| Sheaf.Paper.DerivedTruncationCoproducts | new in U2 delivery | proved public helper; no existing consumers |
| Sheaf.Paper.ProperUnboundedCoproductComparison | new in U2 delivery | proved public helper; no existing consumers |
| Sheaf.SixFunctors.ProperImageLocalizingProper | unchanged; not adapted | sole direct importer; every existing signature and definition identical |

No target meaning changes and no statement review is reopened by a definition change.

## Status

landed 20261019T034307-L-418429 2026-10-19 (merge of deliver/U2/Sheaf.Paper.ProperUnboundedCoproducts)
