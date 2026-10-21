/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E5
-/
module

public import Sheaf.Paper.IntegralModelOpenClosedBasic
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Sheaf.Paper.ContinuousModuleAdjunction

/-!
# Continuous-coefficient restriction on the localized pro-etale site

Source: Stacks Project, Tags 09BN, 00XZ and 03D2
(blueprint: lem-weil-pbc-continuous-module-open-restriction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

set_option backward.isDefEq.respectTransparency false in
private def openSliceEquivalence {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing U.left T) ≌
      SheafOfModules.{u + 1} ((latticeModuleRing X T).over U) := by
  let := Scheme.ProEt.sliceDense X U
  let : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  exact SheafOfModules.pushforwardPushforwardEquivalence (Scheme.ProEt.sliceEquiv X U)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
    (by ext V s; rfl) (by ext V s; rfl)

private def continuousRestriction {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    SheafOfModules.{u + 1} (latticeModuleRing X T) ⥤
      SheafOfModules.{u + 1} (latticeModuleRing U.left T) := by
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  exact SheafOfModules.pushforward (F := G)
    (J := Scheme.ProEt.topology U.left) (K := Scheme.ProEt.topology X)
    (S := latticeModuleRing U.left T) (R := latticeModuleRing X T)
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩

set_option backward.isDefEq.respectTransparency false in
private def continuousRestrictionAdjunction {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousRestriction U T ⊣ continuousModuleDirectImage U.hom T := by
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  let : (Scheme.proEtaleBaseChange U.hom).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology U.left) :=
    Scheme.ProEt.isContinuous_overPullback U.hom
  let a := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ U.hom U.prop trivial
  let φ : latticeModuleRing U.left T ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let ψ : latticeModuleRing X T ⟶
      ((Scheme.proEtaleBaseChange U.hom).sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology U.left)).obj
          (latticeModuleRing U.left T) :=
    (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
        (continuousCoefficientDirectImageMap U.hom T)
  let d := SheafOfModules.pushforwardPushforwardAdj a φ ψ (by rfl) (by
    ext V s
    apply ULift.ext
    ext x
    change s.down ((pullback.lift (𝟙 V.unop.left) V.unop.hom (by simp) ≫
      pullback.fst _ _).base x) = s.down x
    rw [pullback.lift_fst]
    rfl)
  apply d.ofNatIsoRight
  let aT := Scheme.proEtaleSheafAdjunction U.hom CommRingCat.{u + 1}
  have hh : aT.unit.app (latticeCoefficientSheaf X T) ≫
      (Scheme.proEtaleSheafDirectImage U.hom CommRingCat.{u + 1}).map
        (continuousCoefficientInverseImageMap U.hom T) =
      continuousCoefficientDirectImageMap U.hom T := by
    exact (aT.homEquiv _ _).apply_symm_apply
      (continuousCoefficientDirectImageMap U.hom T)
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
    let e (V : X.ProEtᵒᵖ) : ((SheafOfModules.pushforward ψ).obj M).val.obj V ≅
        ((continuousModuleDirectImage U.hom T).obj M).val.obj V := by
      refine
        { hom := ModuleCat.ofHom
            (X := ((SheafOfModules.pushforward ψ).obj M).val.obj V)
            (Y := ((continuousModuleDirectImage U.hom T).obj M).val.obj V)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          inv := ModuleCat.ofHom
            (X := ((continuousModuleDirectImage U.hom T).obj M).val.obj V)
            (Y := ((SheafOfModules.pushforward ψ).obj M).val.obj V)
            { toFun := fun x ↦ x
              map_add' := fun _ _ ↦ rfl
              map_smul' := ?_ }
          hom_inv_id := rfl
          inv_hom_id := rfl }
      all_goals
        intro r x
        have h := congrArg (fun t ↦ t.hom.app V r) hh
        let act := fun s : (latticeModuleRing U.left T).obj.obj
            ((Scheme.proEtaleBaseChange U.hom).op.obj V) ↦
          s • (show M.val.obj ((Scheme.proEtaleBaseChange U.hom).op.obj V) from x)
        first | exact congrArg act h.symm | exact congrArg act h
    exact PresheafOfModules.isoMk e (by intros; ext x; rfl)
  · intro M N f
    ext V x
    rfl

private def restrictionToSlice {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    continuousRestriction U T ⋙ openSliceModules U T ≅
      SheafOfModules.overFunctor (latticeModuleRing X T) U := by
  let G : U.left.ProEt ⥤ X.ProEt := MorphismProperty.Over.map ⊤ U.prop
  let : G.IsContinuous (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap U.prop
  let := Scheme.ProEt.sliceDense X U
  let : (Scheme.ProEt.sliceEquiv X U).functor.IsContinuous
      ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left) := inferInstance
  let H := (Scheme.ProEt.sliceEquiv X U).functor ⋙ G
  let : H.IsContinuous ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology X) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology U.left) _
  let e : H ≅ Over.forget U := NatIso.ofComponents (fun V ↦
    MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ V.left.hom = V.hom.left ≫ U.hom
      simp only [Category.id_comp, MorphismProperty.Over.w])) (by
        intro V W f
        apply MorphismProperty.Over.Hom.ext
        change f.left.left ≫ 𝟙 _ = 𝟙 _ ≫ f.left.left
        simp)
  let φ : (latticeModuleRing X T).over U ⟶
      (H.sheafPushforwardContinuous RingCat.{u + 1}
        ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let ψ : latticeModuleRing U.left T ⟶
      (G.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology U.left) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  let χ : (latticeModuleRing X T).over U ⟶
      ((Scheme.ProEt.sliceEquiv X U).functor.sheafPushforwardContinuous RingCat.{u + 1}
        ((Scheme.ProEt.topology X).over U) (Scheme.ProEt.topology U.left)).obj
          (latticeModuleRing U.left T) :=
    ⟨{ app := fun _ ↦ 𝟙 _
       naturality := fun _ _ _ ↦ rfl }⟩
  refine (SheafOfModules.pushforwardComp χ ψ) ≪≫ ?_
  refine (SheafOfModules.pushforwardCongr ?_) ≪≫
    SheafOfModules.pushforwardCongr₂ φ e.symm (by ext V s; rfl)
  ext V s
  rfl

/-- Restriction of continuous-coefficient modules is the slice restriction functor,
after the explicit equivalence of pro-etale sites.
Source: Stacks Project, Tags 09BN, 00XZ and 03D2
(blueprint: lem-weil-pbc-continuous-module-open-restriction).
Proof: restriction along the forgetful functor from the site over U is left adjoint
to continuous direct image. Construct this adjunction using the map/pullback site
adjunction. Its coefficient compatibility is the triangle identity for continuous
functions. Uniqueness of left adjoints identifies it with the specified ringed
pullback. The slice equivalence sends its sections and scalar actions identically
to those of restriction to the localized site. -/
theorem continuousModule_open_restriction {X : Scheme.{u}} (U : X.ProEt)
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    (c : (Scheme.proEtaleSheafInverseImage U.hom CommRingCat.{u + 1}).obj
      (latticeCoefficientSheaf X T) ≅ latticeCoefficientSheaf U.left T)
    (hc : c.hom = continuousCoefficientInverseImageMap U.hom T) :
    (openSliceModules U T).IsEquivalence ∧
      Nonempty (Scheme.proEtaleRingModulePullback U.hom (latticeCoefficientSheaf X T)
        (latticeCoefficientSheaf U.left T) c ⋙ openSliceModules U T ≅
          SheafOfModules.overFunctor (latticeModuleRing X T) U) := by
  refine ⟨?_, ?_⟩
  · exact inferInstanceAs (openSliceEquivalence U T).functor.IsEquivalence
  · obtain ⟨a⟩ := continuousModule_adjunction U.hom T c hc
    exact ⟨isoWhiskerRight (a.leftAdjointUniq (continuousRestrictionAdjunction U T))
      (openSliceModules U T) ≪≫ restrictionToSlice U T⟩

end AlgebraicGeometry.ProEtale
