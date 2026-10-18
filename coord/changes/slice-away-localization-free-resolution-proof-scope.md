# CategoryTheory.sliceAwayLocalization_free_resolution

## Reason

Preflight flags new `variable` commands in helper sections as potentially visible commands.
All three variable blocks are lexically scoped within sections, every declaration they
supply is private, and each section is closed before the public theorem. The original
universe command, open commands, public imports and public theorem signature are unchanged.
The new imports are proof-only. No public definition or other public declaration is added.
This record makes that scope change explicit for independent review.

## Old

The public signature, verbatim:

```lean
theorem sliceAwayLocalization_free_resolution {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U))
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ∃ L : SliceAwayLocalization O U f,
    ∃ d : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            O).over U))
            (ULift.{u} ℕ)),
    ∃ q : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (PresheafOfModules.sheafification (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            O).over U).obj)).obj L.val,
      (∃ h : d ≫ q = 0, (ShortComplex.mk
        (C := ringedSiteModules
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).over U))
        d q h).ShortExact) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        d.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up n)).val.app V a -
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up (n + 1))).val.app V
            (O.obj.map V.unop.hom.op f * a)) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        q.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (((sheafCompose J (forget₂ CommRingCat
              RingCat)).obj O).over U).obj)).unit.app
            L.val).app V ((L.equiv V).symm
              (algebraMap _ _ a * IsLocalization.Away.invSelf
                (O.obj.map V.unop.hom.op f) ^ n)))
```

## New

The public signature is identical, verbatim:

```lean
theorem sliceAwayLocalization_free_resolution {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (O : Sheaf J CommRingCat.{u}) (U : C)
    (f : O.obj.obj (op U))
    [HasSheafify (J.over U) AddCommGrpCat.{u}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    ∃ L : SliceAwayLocalization O U f,
    ∃ d : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
            O).over U))
            (ULift.{u} ℕ)),
    ∃ q : (SheafOfModules.free (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
        O).over
        U)) (ULift.{u} ℕ)) ⟶
        (PresheafOfModules.sheafification (𝟙 (((sheafCompose J (forget₂ CommRingCat.{u}
            RingCat.{u})).obj
            O).over U).obj)).obj L.val,
      (∃ h : d ≫ q = 0, (ShortComplex.mk
        (C := ringedSiteModules
          (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj O).over U))
        d q h).ShortExact) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        d.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up n)).val.app V a -
          (SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj
              O).over
              U)) (ULift.up (n + 1))).val.app V
            (O.obj.map V.unop.hom.op f * a)) ∧
      (∀ (V : (Over U)ᵒᵖ) (n : ℕ) (a : O.obj.obj (op V.unop.left)),
        q.val.app V ((SheafOfModules.ιFree (R := (((sheafCompose J (forget₂ CommRingCat
            RingCat)).obj O).over U)) (ULift.up n)).val.app V a) =
          ((PresheafOfModules.sheafificationAdjunction (𝟙 (((sheafCompose J (forget₂ CommRingCat
              RingCat)).obj O).over U).obj)).unit.app
            L.val).app V ((L.equiv V).symm
              (algebraMap _ _ a * IsLocalization.Away.invSelf
                (O.obj.map V.unop.hom.op f) ^ n)))
```

The following additional variable contexts are confined to separate helper sections:

```lean
variable {R : Type u} [CommRing R]
```

```lean
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (O : Sheaf J CommRingCat.{u}) (U : C) (f : O.obj.obj (op U))
```

```lean
variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
```

The public proof now constructs the localization and telescope maps and proves short
exactness and the two coordinate identities, replacing its original sorry.
The helper definitions contain explicit data and proved laws.

## Users

`tools/downstream.py Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution --uses
sliceAwayLocalization_free_resolution` lists the seven downstream modules below. Its
textual uses scan finds no external use of the theorem yet: its parent imports the module
as a proof dependency. No consumer needs adaptation; every original signature and public
visibility remains identical. No target meaning changes, and no target review is reopened.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FlatRingedIdealCompleteEquivalence | M1 | No change; no adaptation. |
| Sheaf.Paper.LocalHomTowerCriterion | M4 | No change; no adaptation. |
| Sheaf.Paper.RestrictionLocalCompleteness | A2 | No change; no adaptation. |
| Sheaf.RingTheory.DerivedCompleteProductsTriangles | B2 | No change; no adaptation. |
| Sheaf.RingTheory.ModuleLocalizationTowerVanishing | H1 | No change; no adaptation. |
| Sheaf.RingTheory.NilpotentTorsionDerivedLimitComplete | Q1 | No change; no adaptation. |
| Sheaf.RingTheory.RlimPerfectComplete | R1 | No change; no adaptation. |

Only `Sheaf.Paper.LocalHomTowerCriterion` imports the item directly; the remaining entries
are transitive consumers. The original direct consumer is compiled against the delivered
module as the consumer check. Claim holders were read through `stage3_delivery.claim_holder`.

## Status

landed 20261018T062947-L-690858 2026-10-18 (merge of deliver/X2/Sheaf.CategoryTheory.SliceAwayLocalizationFreeResolution)
