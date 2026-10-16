/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.ContinuousCoefficientModuleEncoding

/-! # Restriction of continuous module encodings

Source: Bhatt--Scholze, Section 6.8; Stacks Project, Modules on Sites.
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction)
-/

@[expose] public section

universe u v
open CategoryTheory Opposite MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry.ProEtale
open Scheme MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Limits

private noncomputable abbrev encoding_localization_comparison
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f] :
    (f)^*[Ab.{u + 1}] ≅
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
        Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
  upperStarIsoLocalizationRestriction Ab.{u + 1} f inferInstance

/-- Specialization of the monoidal localization comparison to abelian sheaves.
The general proof is in UpperLowerStar.InternalHom, which cannot be imported here:
it duplicates laxBraided_upperStar from ModuleObject.UpperLowerStar.Monoidal.
We prove this specialization using the same adjunction unit calculations.
Source: the cited source-library module; Stacks Project, Tag 03DO.
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction) -/
private theorem encoding_localization_monoidal
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f] :
    NatTrans.IsMonoidal
      (encoding_localization_comparison X Y f).hom := by
  let h : WeaklyEtale f := inferInstance
  have unit_app
      (P : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (U : X.ProEtᵒᵖ) :
      ((sheafToPresheaf _ Ab.{u + 1}).map
        ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app P)).app U =
        P.obj.map ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f h trivial).counit.app
          U.unop).op := by
    simp [localizationRestrictionLowerStarAdjunction, Adjunction.sheafPushforwardContinuous,
      Adjunction.whiskerLeft]
  have unit_tensor
      (P Q : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app (P ⊗ Q) =
        ((localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app P ⊗ₘ
          (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app Q) ≫
          μ (f)_*[Ab.{u + 1}] _ _ ≫ (f)_*[Ab.{u + 1}].map
            (μ ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
            Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)) P Q) := by
    apply Sheaf.tensor_hom_ext
    rw [Functor.map_comp, ← μ_natural_assoc]
    ext U : 2
    simp only [NatTrans.comp_app, Functor.map_comp, Monoidal.tensorHom_app,
      unit_app]
    erw [← (μ (sheafToPresheaf (ProEt.topology X) Ab.{u + 1}) P Q).naturality]
    erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app_assoc]
    erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
      (F := MorphismProperty.Over.map ⊤ h)]
    rfl
  have unit_unit :
      (localizationRestrictionLowerStarAdjunction Ab.{u + 1} f h).unit.app (𝟙_ _) =
        ε (f)_*[Ab.{u + 1}] ≫ (f)_*[Ab.{u + 1}].map
          (ε ((MorphismProperty.Over.map ⊤ h).sheafPushforwardContinuous
            Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X))) := by
    apply Sheaf.hom_ext_of_ε_comp
    ext U : 2
    simp only [NatTrans.comp_app, Functor.map_comp,
      unit_app]
    erw [← (ε (sheafToPresheaf (ProEt.topology X) Ab.{u + 1})).naturality]
    erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app_assoc]
    erw [Functor.ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app
      (F := MorphismProperty.Over.map ⊤ h)]
    erw [Monoidal.tensorUnit_map, Category.id_comp]
    rfl
  exact {
    unit := by
      rw [← cancel_epi (η (f)^*[Ab.{u + 1}])]
      simp only [Functor.Monoidal.η_ε_assoc]
      apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
      dsimp only [encoding_localization_comparison, upperStarIsoLocalizationRestriction]
      erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rw [Adjunction.homEquiv_unit, Functor.map_comp,
        ← Category.assoc, Adjunction.unit_app_unit_comp_map_η]
      exact unit_unit
    tensor P Q := by
      rw [← cancel_epi (δ (f)^*[Ab.{u + 1}] P Q)]
      simp only [Functor.Monoidal.δ_μ_assoc]
      apply ((upperStarLowerStarAdjunction Ab.{u + 1} f).homEquiv _ _).injective
      dsimp only [encoding_localization_comparison, upperStarIsoLocalizationRestriction]
      erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
      rw [Adjunction.homEquiv_unit, Functor.map_comp,
        ← Category.assoc, Adjunction.unit_app_tensor_comp_map_δ, Functor.map_comp, Category.assoc,
        ← μ_natural_assoc, tensorHom_comp_tensorHom_assoc, Adjunction.unit_leftAdjointUniq_hom_app,
        Adjunction.unit_leftAdjointUniq_hom_app]
      exact unit_tensor P Q }

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- Restriction of a continuous-function coefficient ring is identity on sections.
Source: Bhatt--Scholze, Section 6.8.
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction) -/
noncomputable def continuousRestrictionMap
    {X Y : Scheme.{u}} (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] :
    (continuousMapRingSheaf Y T).obj ⟶
      (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).op ⋙
        (continuousMapRingSheaf X T).obj :=
  { app := fun _ ↦ 𝟙 _
    naturality := fun _ _ _ ↦ rfl }

/-- Encoding canonical inverse image agrees with restriction of the sectionwise module.
Source: Bhatt--Scholze, Section 6.8; Stacks Project, Tags 03EK and 03EL.
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction)

Proof. Apply the monoidal localization comparison to the underlying module.
Conjugate its coefficient map by the two continuous charts. The chart-pullback
square identifies the result with the identity continuous-function coefficient
map. Evaluating the actions on pure tensors gives the sectionwise linearity.
Naturality is the localization comparison's naturality. -/
theorem continuousRing_module_restriction
    (X Y : Scheme.{u}) (f : Y ⟶ X) [WeaklyEtale f]
    (T : Type) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj T) X)) :
    Nonempty (((continuousRingModuleEquivalence Y T).functor.obj
        ((upperStar (Profinite.continuousMapRingObj T) f).obj P)).val ≅
      (PresheafOfModules.pushforward (continuousRestrictionMap f T)).obj
        ((continuousRingModuleEquivalence X T).functor.obj P).val) := by
  let G := ProEtale.upperStar Ab.{u + 1} f
  let L := (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)).sheafPushforwardContinuous
    Ab.{u + 1} (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
  let τ := ProEtale.encoding_localization_comparison X Y f
  let cX := chartComparison X T
  let cY := chartComparison Y T
  let : IsIso cX := chartComparison_isIso X T
  let : IsIso cY := chartComparison_isIso Y T
  let : NatTrans.IsMonoidal τ.hom := ProEtale.encoding_localization_monoidal X Y f
  let φ := condensedPullbackHom (Profinite.continuousMapRingObj T) f
  let A := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj (continuousMapRingSheaf X T)
  let C := condensedRingObj (Profinite.continuousMapRingObj T) X
  let : MonObj C := inferInstanceAs
    (MonObj (condensedRingObj (Profinite.continuousMapRingObj T) X))
  have hs : G.map cX ≫ τ.hom.app A = φ ≫ cY := continuousChart_pullback X Y f T
  have hc : (inv cY ≫ inv φ) ≫ τ.hom.app C = L.map (inv cX) := by
    apply (cancel_epi (φ ≫ cY)).mp
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    calc
      τ.hom.app C = G.map cX ≫ τ.hom.app A ≫ L.map (inv cX) := by
        rw [← τ.hom.naturality]
        simp
        rfl
      _ = φ ≫ cY ≫ L.map (inv cX) := by rw [← Category.assoc, hs, Category.assoc]
  let : IsMonHom (τ.hom.app C) := NatTrans.isMonHom_app τ.hom C
  let Q := (G.mapMod C).obj P
  let ψ := inv cY ≫ inv φ
  let e := (Functor.mapModNatIso τ C).app P
  let Q' := (Mod.comap ψ).obj Q
  let Q'' := (Mod.comap ψ).obj ((Mod.comap (τ.hom.app C)).obj ((L.mapMod C).obj P))
  let R := continuousMapRingSheaf Y T
  let AY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  let : IsCommMonObj AY := Sheaf.isCommMonObj_sheafCompose_obj _ R
    (fun V a b ↦ by exact @mul_comm (ULift C(V.unop.left, T)) inferInstance a b)
  let H := (InternalAbelianSheafModule.sectionModuleEquivalence
    (Scheme.ProEt.topology Y) AY).functor ⋙
      (ringModuleEquivalenceOfIso Y (reconstructedRingIso Y R).symm).functor
  let e₀ := ((Mod.comap (inv cY)).mapIso ((Mod.extendScalarsIsoComapInv φ).app Q)) ≪≫
    ((Mod.comapComp (inv cY) (inv φ)).app Q).symm ≪≫
      (Mod.comap ψ).mapIso e
  refine ⟨((SheafOfModules.forget _).mapIso (H.mapIso e₀)) ≪≫ ?_⟩
  refine PresheafOfModules.isoMk (fun Z ↦ ?_) ?_
  · refine ModuleCat.isoMk (Iso.refl _) ?_
    intro r
    ext m
    let Z' := (MorphismProperty.Over.map ⊤
      (inferInstance : WeaklyEtale f)).op.obj Z
    have ha :
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
          AY (L.obj P.X)).app Z ≫
          (ψ ▷ _ ≫ (τ.hom.app C) ▷ _ ≫
            Functor.LaxMonoidal.μ L C P.X ≫ L.map (Mod.act P.X)).hom.app Z =
        (Functor.LaxMonoidal.μ (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1})
          A P.X).app Z' ≫ ((inv cX) ▷ P.X ≫ Mod.act P.X).hom.app Z' := by
      have hh : ψ ▷ L.obj P.X ≫ (τ.hom.app C) ▷ L.obj P.X =
          (L.map (inv cX)) ▷ L.obj P.X := by
        rw [← comp_whiskerRight]
        exact congrArg (fun a ↦ a ▷ L.obj P.X) hc
      rw [← Category.assoc (ψ ▷ _) ((τ.hom.app C) ▷ _) _, hh]
      rw [Functor.LaxMonoidal.μ_natural_left_assoc L (inv cX) P.X,
        ← Functor.map_comp]
      simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app]
      rw [← Category.assoc]
      erw [Functor.μ_sheafToPresheaf_app_comp_μ_sheafPushforwardContinuous_app
          (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)) Ab.{u + 1}
          (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) A P.X Z]
      rfl
    exact ConcreteCategory.congr_hom ha.symm (r ⊗ₜ[ℤ] m)
  · intro Z W a
    ext m
    rfl

private theorem coefficientCast_app
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    {R S : Sheaf J CommRingCat.{u + 1}} (h : R = S) (Z : Cᵒᵖ) :
    ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (eqToHom h)).hom.app Z =
      eqToHom (congrArg (fun R : Sheaf J CommRingCat.{u + 1} ↦
        ((sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj.obj Z) h) := by
  subst h
  simp

/-- The rational encoding commutes with the etale restriction used in a lattice.
Source: Bhatt--Scholze, Proposition 6.8.4(6).
(blueprint: lem-weil-pbc-continuous-module-encoding-restriction)

Proof. Apply continuousRing_module_restriction and transport its coefficient
rings through lisseFieldSheaf_eq. These transports commute with restriction
because they are induced by the same equality of coefficient topologies. -/
theorem continuousField_module_restriction
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (X Y : Scheme.{u}) (f : Y ⟶ X) [Etale f]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj E) X)) :
    Nonempty (((continuousFieldModuleEquivalence ℓ E Y).functor.obj
        ((upperStar (Profinite.continuousMapRingObj E) f).obj P)).val ≅
      (PresheafOfModules.pushforward (lisseEtaleCoefficientIdentification ℓ E f)).obj
        ((continuousFieldModuleEquivalence ℓ E X).functor.obj P).val) := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let : TotallySeparatedSpace E :=
    totallySeparatedSpace_iff_exists_isClopen.mpr fun x y h ↦ by
      obtain ⟨r, hr, hr'⟩ := exists_between (dist_pos.mpr h)
      refine ⟨_, IsUltrametricDist.isClopen_ball x r, ?_, ?_⟩
      · simp only [Metric.mem_ball, dist_self, hr]
      · simp only [Set.mem_compl, Metric.mem_ball, dist_comm, not_lt, hr'.le]
  obtain ⟨e⟩ := continuousRing_module_restriction X Y f E P
  let eY := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E Y))
  let eX := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq ℓ E X))
  refine ⟨PresheafOfModules.isoMk (fun Z ↦ ?_) ?_⟩
  · let eZ := (PresheafOfModules.evaluation _ Z).mapIso e
    refine ModuleCat.isoMk ((forget₂ (ModuleCat ((continuousMapRingSheaf Y E).obj.obj Z))
      Ab.{u + 1}).mapIso eZ) ?_
    intro r
    ext m
    let Z' := (lisseEtaleSiteInclusion f).op.obj Z
    have hh : eX.hom.hom.app Z' = eY.hom.hom.app Z := by
      change ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (eqToHom (lisseFieldSheaf_eq ℓ E X))).hom.app Z' =
        ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
            (eqToHom (lisseFieldSheaf_eq ℓ E Y))).hom.app Z
      rw [coefficientCast_app, coefficientCast_app]
    change (eX.hom.hom.app Z' r) • (e.hom.app Z m) =
      e.hom.app Z ((eY.hom.hom.app Z r) •
        (show ((continuousRingModuleEquivalence Y E).functor.obj
          ((upperStar (Profinite.continuousMapRingObj E) f).obj P)).val.obj Z from m))
    rw [hh]
    exact ((e.hom.app Z).hom.map_smul _ _).symm
  · intro Z W a
    ext m
    exact PresheafOfModules.naturality_apply e.hom a m

end AlgebraicGeometry.ProEtale.CondensedRing
