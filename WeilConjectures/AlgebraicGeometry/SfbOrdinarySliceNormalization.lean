/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
public import WeilConjectures.AlgebraicGeometry.AdicStratumCompletionUnit
import all WeilConjectures.Algebra.Homology.SitePerfectModelRestriction
import all WeilConjectures.AlgebraicGeometry.ConstantCompletionCore
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction

/-! # Ordinary module comparisons for normalized restriction

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D3](https://stacks.math.columbia.edu/tag/03D3)
* [Stacks Project, Tag 00YY](https://stacks.math.columbia.edu/tag/00YY)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private noncomputable def resIdIso
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u + 1}) :
    ConstantCompletion.res (𝟙 R) ≅ 𝟭 (ConstantCompletion.Mod R) := Iso.refl _

private noncomputable def scalarEquivalence
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ≅ S) :
    ConstantCompletion.Mod S ≌ ConstantCompletion.Mod R :=
  CategoryTheory.Equivalence.mk (ConstantCompletion.res c.hom) (ConstantCompletion.res c.inv)
    (ConstantCompletion.resCompIso c.inv c.hom (𝟙 S) c.inv_hom_id ≪≫ resIdIso S).symm
    (ConstantCompletion.resCompIso c.hom c.inv (𝟙 R) c.hom_inv_id ≪≫ resIdIso R)

private noncomputable def changeIsoRestriction
    {C : Type (u + 1)} [SmallCategory C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (c : R ⟶ S) [IsIso c] :
    ConstantCompletion.change c ≅ ConstantCompletion.res (asIso c).inv := by
  let E := scalarEquivalence (asIso c)
  exact (SheafOfModules.tensorAdjunction c).leftAdjointUniq E.symm.toAdjunction

set_option maxHeartbeats 800000 in
-- The final transport compares module structures on the two site presentations.
/-- Ordinary slice restriction commutes with transport to the AsSmall site and
with an invertible change of coefficient rings. -/
theorem sfbOrdinarySliceNormalization
    (S : Scheme.{u}) (U : S.ProEt)
    (R : Sheaf (ProEt.topology S) CommRingCat.{u + 1})
    (B : Sheaf (proEtaleModelTopology S) CommRingCat.{u + 1})
    (T : Sheaf ((proEtaleModelTopology S).over (AsSmall.up.obj U))
      CommRingCat.{u + 1})
    (e : (sfbModelRings S).obj R ≅ B)
    (c : ((SfbAdicRestriction.sliceAlgebra (proEtaleModelTopology S)
      (AsSmall.up.obj U)).rings.obj B) ⟶ T) [IsIso c] :
    ∃ G : SheafOfModules.{u + 1} (((adicLisseForget S).obj R).over U) ⥤
        ConstantCompletion.Mod T,
      G.Additive ∧ PreservesFiniteLimits G ∧ PreservesFiniteColimits G ∧
      Nonempty
        ((proEtaleModuleToModel ((adicLisseForget S).obj R) ⋙
            ConstantCompletion.res e.inv) ⋙
            ConstantCompletion.pull
              (SfbAdicRestriction.sliceAlgebra (proEtaleModelTopology S)
                (AsSmall.up.obj U)) c ≅
          SheafOfModules.overFunctor ((adicLisseForget S).obj R) U ⋙ G) := by
  let J := proEtaleModelTopology S
  let W : proEtaleSiteModel S := AsSmall.up.obj U
  let E := Over.postEquiv (X := W)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).symm
  let H : Over W ⥤ Over U := E.functor
  have : (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt).IsDenseSubsite
      J (ProEt.topology S) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.IsDenseSubsite
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.inducedTopology
        (ProEt.topology S)) (ProEt.topology S))
  have : (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).IsDenseSubsite
      (ProEt.topology S) J :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).functor.IsDenseSubsite
      (ProEt.topology S)
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := S.ProEt)).inverse.inducedTopology
        (ProEt.topology S)))
  have : (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt).IsCocontinuous
      J (ProEt.topology S) := by infer_instance
  have : (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S).IsCocontinuous
      (ProEt.topology S) J := by infer_instance
  have hH : E.functor.IsCocontinuous (J.over W) ((ProEt.topology S).over U) := by
    change (Over.post (X := W)
      (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt)).IsCocontinuous _ _
    exact inferInstanceAs ((Over.post (X := W)
      (AsSmall.down : proEtaleSiteModel S ⥤ S.ProEt)).IsCocontinuous
        (J.over W) ((ProEt.topology S).over (AsSmall.down.obj W)))
  have : H.IsEquivalence := inferInstanceAs E.functor.IsEquivalence
  have hE : E.inverse.IsCocontinuous ((ProEt.topology S).over U) (J.over W) := by
    change (Over.post (X := U) (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S) ⋙
      Over.map (𝟙 W)).IsCocontinuous _ _
    have hp : (Over.post (X := U)
        (AsSmall.up : S.ProEt ⥤ proEtaleSiteModel S)).IsCocontinuous
        ((ProEt.topology S).over U) (J.over (AsSmall.up.obj U)) := inferInstance
    have : (Over.map (𝟙 W)).IsCocontinuous (J.over W) (J.over W) := inferInstance
    exact CategoryTheory.isCocontinuous_comp _ _ ((ProEt.topology S).over U)
      (J.over W)
  have : E.inverse.IsDenseSubsite ((ProEt.topology S).over U) (J.over W) :=
    E.isDenseSubsite_inverse_of_isCocontinuous (J.over W) ((ProEt.topology S).over U)
  have : H.IsContinuous (J.over W) ((ProEt.topology S).over U) :=
    inferInstanceAs (E.functor.IsContinuous (J.over W) ((ProEt.topology S).over U))
  have : H.IsCocontinuous (J.over W) ((ProEt.topology S).over U) := hH
  let φ : siteModuleRings T ⟶
      (H.sheafPushforwardContinuous RingCat.{u + 1}
        (J.over W) ((ProEt.topology S).over U)).obj
        (((adicLisseForget S).obj R).over U) :=
    (sheafCompose (J.over W) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      ((asIso c).inv ≫ (J.overPullback CommRingCat.{u + 1} W).map e.inv)
  let G := SheafOfModules.pushforward.{u + 1} (F := H) φ
  have hGa : G.Additive := ⟨by intros; ext V x; rfl⟩
  have hGl : PreservesFiniteLimits G := SheafOfModules.pushforward_finiteLimits φ
  have hGc : PreservesFiniteColimits G := SheafOfModules.pushforward_finiteColimits φ
  refine ⟨G, hGa, hGl, hGc, ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft
    ((proEtaleModuleToModel ((adicLisseForget S).obj R) ⋙
      ConstantCompletion.res e.inv) ⋙ SheafOfModules.overFunctor (siteModuleRings B) W)
    (changeIsoRestriction c)

end AlgebraicGeometry.Scheme
