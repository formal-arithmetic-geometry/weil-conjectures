/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk

/-!
# Blueprint statements

lem-weil-pbc-retract-supplied.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Blueprint: lem-weil-pbc-retract-supplied. -/
theorem Etale.exists_injective_retract_of_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    (Λ : Type (u + 1)) [CommRing Λ] :
    (fun (RV : Sheaf Y.smallEtaleTopology RingCat.{u + 1})
      (RU : Sheaf X.smallEtaleTopology RingCat.{u + 1})
      (etaV : (Functor.const Y.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ RV.obj)
      (etaU : (Functor.const X.Etaleᵒᵖ).obj (RingCat.of Λ) ⟶ RU.obj) ↦
    ∀ (gamma : RV ⟶ ((MorphismProperty.Over.pullback @Etale ⊤ f).sheafPushforwardContinuous
        RingCat.{u + 1} (Y.smallGrothendieckTopology @Etale)
        (X.smallGrothendieckTopology @Etale)).obj RU),
    (∀ (W : Y.Etaleᵒᵖ) (r : Λ),
        gamma.hom.app W (etaV.app W r) =
          etaU.app ((MorphismProperty.Over.pullback @Etale ⊤ f).op.obj W) r) →
    ∀ (LM : SheafOfModules.{u + 1} RV ⥤ SheafOfModules.{u + 1} RU)
      (am : LM ⊣ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma))
      (e : LM ⋙ SheafOfModules.toSheaf RU ≅
        SheafOfModules.toSheaf RV ⋙ Etale.upperStar AddCommGrpCat.{u + 1} f),
    (∀ G : SheafOfModules.{u + 1} RV,
      (SheafOfModules.toSheaf RV).map (am.unit.app G) =
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((SheafOfModules.toSheaf RV).obj G) ≫
            (Etale.lowerStar AddCommGrpCat.{u + 1} f).map (e.inv.app G)) →
    ∀ (I : SheafOfModules.{u + 1} RV) [Injective I]
      (J : SheafOfModules.{u + 1} RU) (j : LM.obj I ⟶ J) [Mono j],
    Mono (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ∧
      ∃ (rho : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ⟶ I)
        (pi : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ⟶ kernel rho)
        (s : (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).obj J ≅ I ⨯ kernel rho),
        (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ≫ rho = 𝟙 I ∧
        pi ≫ kernel.ι rho = 𝟙 _ -
          rho ≫ (am.unit.app I ≫ (SheafOfModules.pushforward
        (J := Y.smallGrothendieckTopology @Etale)
        (K := X.smallGrothendieckTopology @Etale)
        (F := MorphismProperty.Over.pullback @Etale ⊤ f) gamma).map j) ∧
        s.hom = prod.lift rho pi)
      ((sheafCompose Y.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf Y.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)))
      ((sheafCompose X.smallEtaleTopology (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((constantSheaf X.smallEtaleTopology CommRingCat.{u + 1}).obj (CommRingCat.of Λ)))
      (Functor.whiskerRight
        (toSheafify Y.smallEtaleTopology ((Functor.const Y.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
      (Functor.whiskerRight
        (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj (CommRingCat.of Λ)))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})) := by
  sorry

end AlgebraicGeometry
