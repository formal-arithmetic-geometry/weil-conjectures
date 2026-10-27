# SheafOfModules.generalizedTensorNormalization_unit_equation

## Reason

Preflight requests a change record because the theorem's source spelling now supplies
already-inferred implicit parameters explicitly. This is an elaboration performance repair:
`J`, `K`, `R₁`, `R₂`, `A` and `B` are fixed to the sites and rings already determined by the
existing arguments. No binder, hypothesis, conclusion, universe parameter, declaration name,
visibility or public import is added, removed or mathematically changed. There is no definition
change and no target statement or target meaning changes.

The file also adds local irreducibility attributes for module sheafification, its adjunction
and its tensor comparison, and a local elaborator transparency option. These affect elaboration
inside this file only. Five proved private helpers implement the pure-section calculation.
The proof-only import of TensorBilinearUniversal is replaced by CartesianMonoidal.

The previous source spelling caused repeated inference and unfolding of sheafification
interfaces; the final explicitly typed counit version compiled in 52.1 seconds, with zero
holes. Delivery then passed its initial compile and reached the record gate at server preflight.

## Old

```lean
theorem generalizedTensorNormalization_unit_equation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{w}) (A S : Sheaf JD CommRingCat.{w})
    (F : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (adj : F ⊣ v.sheafPushforwardContinuous (Type w) JC JD)
    [PreservesFiniteLimits F]
    (I : AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} F R A)
    (α : A ⟶ S)
    (c : ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{w} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hc : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      ULift.up (c.hom.app U r) =
        (adj.homEquiv _ _ (I.ringUnderlying.hom ≫
          (sheafCompose JD (CategoryTheory.forget CommRingCat.{w} ⋙
            uliftFunctor.{w, w})).map α)).hom.app U (ULift.up r))
    (η : ∀ X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      X ⟶ (pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
        (changeOfRings.{vD, uD, w} α (I.modules.obj X)))
    (heta : ∀ (X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (U : Cᵒᵖ) (x : X.val.obj U),
      (η X).val.app U x = ringedComparisonScalarSection.{w, uD, vD} α (I.modules.obj X)
        (v.op.obj U) 1
        (((I.moduleUnderlying.inv.app X).hom.app (v.op.obj U)
          ((adj.unit.app ((toSheaf
            ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
            (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj X)).hom.app
              U (ULift.up x))).down))
    (M N : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (p : (monoidalCategory.{vC, uC, w} R).tensorObj
      ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
        (changeOfRings.{vD, uD, w} α (I.modules.obj M)))
      ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
        (changeOfRings.{vD, uD, w} α (I.modules.obj N))) ⟶
      (pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
      ((monoidalCategory.{vD, uD, w} S).tensorObj
        (changeOfRings.{vD, uD, w} α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} α (I.modules.obj N))))
    (hpairing : ∀ (U : Cᵒᵖ)
      (m : ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
        (changeOfRings.{vD, uD, w} α (I.modules.obj M))).val.obj U)
      (n : ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
        (changeOfRings.{vD, uD, w} α (I.modules.obj N))).val.obj U),
      p.val.app U (ringedComparisonPure.{w, uC, vC} R
        ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
          (changeOfRings.{vD, uD, w} α (I.modules.obj M)))
        ((pushforward.{w, vC, vD, uC, uD, w} (F := v) c).obj
          (changeOfRings.{vD, uD, w} α (I.modules.obj N))) U m n) =
        ringedComparisonPure.{w, uD, vD} S
          (changeOfRings.{vD, uD, w} α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} α (I.modules.obj N)) (v.op.obj U) m n)
    (μ : changeOfRings.{vD, uD, w} α
      (I.modules.obj ((monoidalCategory.{vC, uC, w} R).tensorObj M N)) ⟶
      (monoidalCategory.{vD, uD, w} S).tensorObj
        (changeOfRings.{vD, uD, w} α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} α (I.modules.obj N)))
    (hnormalize : ∀ (Z : Sheaf JC (Type w))
      (x : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj M)
      (y : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj N)
      (z : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj
          ((monoidalCategory.{vC, uC, w} R).tensorObj M N)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        (z.hom.app U t).down = ringedComparisonPure.{w, uC, vC} R M N U
          (x.hom.app U t).down (y.hom.app U t).down) →
      ∀ (V : Dᵒᵖ) (t : (F.obj Z).obj.obj V),
        μ.val.app V
          (ringedComparisonScalarSection.{w, uD, vD} α
            (I.modules.obj ((monoidalCategory.{vC, uC, w} R).tensorObj M N)) V 1
            (((I.moduleUnderlying.inv.app
              ((monoidalCategory.{vC, uC, w} R).tensorObj M N)).hom.app V
              ((F.map z).hom.app V t)).down)) =
        ringedComparisonPure.{w, uD, vD} S
          (changeOfRings.{vD, uD, w} α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} α (I.modules.obj N)) V
          (ringedComparisonScalarSection.{w, uD, vD} α (I.modules.obj M) V 1
            (((I.moduleUnderlying.inv.app M).hom.app V ((F.map x).hom.app V t)).down))
          (ringedComparisonScalarSection.{w, uD, vD} α (I.modules.obj N) V 1
            (((I.moduleUnderlying.inv.app N).hom.app V ((F.map y).hom.app V t)).down))) :
    η ((monoidalCategory.{vC, uC, w} R).tensorObj M N) ≫
      (pushforward.{w, vC, vD, uC, uD, w} (F := v) c).map μ =
      (monoidalCategory.{vC, uC, w} R).tensorHom (η M) (η N) ≫ p
```

## New

```lean
theorem generalizedTensorNormalization_unit_equation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{w} C] [EssentiallySmall.{w} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{w}) (A S : Sheaf JD CommRingCat.{w})
    (F : Sheaf JC (Type w) ⥤ Sheaf JD (Type w))
    (adj : F ⊣ v.sheafPushforwardContinuous (Type w) JC JD)
    [PreservesFiniteLimits F]
    (I : AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} F R A)
    (α : A ⟶ S)
    (c : ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{w} JC JD).obj
        ((sheafCompose JD (forget₂ CommRingCat.{w} RingCat.{w})).obj S))
    (hc : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      ULift.up (c.hom.app U r) =
        (adj.homEquiv _ _ (I.ringUnderlying.hom ≫
          (sheafCompose JD (CategoryTheory.forget CommRingCat.{w} ⋙
            uliftFunctor.{w, w})).map α)).hom.app U (ULift.up r))
    (η : ∀ X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R),
      X ⟶ (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj X)))
    (heta : ∀ (X : SheafOfModules.{w}
      ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
      (U : Cᵒᵖ) (x : X.val.obj U),
      (η X).val.app U x =
        ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α (I.modules.obj X)
        (v.op.obj U) 1
        (((I.moduleUnderlying.inv.app X).hom.app (v.op.obj U)
          ((adj.unit.app ((toSheaf
            ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
            (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj X)).hom.app
              U (ULift.up x))).down))
    (M N : SheafOfModules.{w} ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R))
    (p : (monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj
      ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M)))
      ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))) ⟶
      (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
      ((monoidalCategory.{vD, uD, w} (J := JD) S).tensorObj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))))
    (hpairing : ∀ (U : Cᵒᵖ)
      (m : ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))).val.obj U)
      (n : ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))).val.obj U),
      p.val.app U (ringedComparisonPure.{w, uC, vC} (J := JC) R
        ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M)))
        ((pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).obj
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N))) U m n) =
        ringedComparisonPure.{w, uD, vD} (J := JD) S
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)) (v.op.obj U) m n)
    (μ : changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
      (I.modules.obj ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)) ⟶
      (monoidalCategory.{vD, uD, w} (J := JD) S).tensorObj
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
        (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)))
    (hnormalize : ∀ (Z : Sheaf JC (Type w))
      (x : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj M)
      (y : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj N)
      (z : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{w} RingCat.{w})).obj R) ⋙
        sheafCompose JC
        (CategoryTheory.forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w})).obj
          ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)),
      (∀ (U : Cᵒᵖ) (t : Z.obj.obj U),
        (z.hom.app U t).down = ringedComparisonPure.{w, uC, vC} (J := JC) R M N U
          (x.hom.app U t).down (y.hom.app U t).down) →
      ∀ (V : Dᵒᵖ) (t : (F.obj Z).obj.obj V),
        μ.val.app V
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)) V 1
            (((I.moduleUnderlying.inv.app
              ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N)).hom.app V
              ((F.map z).hom.app V t)).down)) =
        ringedComparisonPure.{w, uD, vD} (J := JD) S
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α (I.modules.obj M))
          (changeOfRings.{vD, uD, w} (J := JD) (R₁ := A) (R₂ := S) α
            (I.modules.obj N)) V
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj M) V 1
            (((I.moduleUnderlying.inv.app M).hom.app V ((F.map x).hom.app V t)).down))
          (ringedComparisonScalarSection.{w, uD, vD} (J := JD) (A := A) (B := S) α
            (I.modules.obj N) V 1
            (((I.moduleUnderlying.inv.app N).hom.app V ((F.map y).hom.app V t)).down))) :
    η ((monoidalCategory.{vC, uC, w} (J := JC) R).tensorObj M N) ≫
      (pushforward.{w, vC, vD, uC, uD, w} (J := JC) (K := JD) (F := v) c).map μ =
      (monoidalCategory.{vC, uC, w} (J := JC) R).tensorHom (η M) (η N) ≫ p
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeneralizedTensorNormalizationUnitEquation | K6 | Close the existing theorem's hole; spell inferred implicit arguments explicitly. |

`python3 tools/downstream.py Sheaf.Paper.GeneralizedTensorNormalizationUnitEquation --uses
SheafOfModules.generalizedTensorNormalization_unit_equation` reports zero downstream modules
and only the item's own declaration as a name hit. Searching both library roots and quarantine
finds the same result. There are no current Lean consumers to adapt. The DAG parents remain:
this record does not withdraw the item or remove its Lean attachment. Since the mathematical
statement is unchanged, the node's statement and statement dependencies stay unchanged.

## Status

landed 20261023T231715-L-3635554 2026-10-23 (merge of deliver/K6/Sheaf.Paper.GeneralizedTensorNormalizationUnitEquation)
