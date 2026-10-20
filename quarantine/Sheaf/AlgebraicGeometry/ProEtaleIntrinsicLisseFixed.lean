/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D7
-/
module

public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.ProEtaleLisseOrigin
public import Sheaf.AlgebraicGeometry.ProEtaleModuleStalkFunctor
import Sheaf.Paper.ProEtaleConstantModuleEncoding
import WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Sheaf.Paper.ProEtaleFiniteModelStalks
import Sheaf.Paper.ProEtaleFiniteModelLocalConstancy
import Sheaf.Paper.ProEtaleLisseFiniteModelsFromLisse

/-! # Finite lisse sheaves in the two constant-coefficient presentations -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

namespace ConstantScalarComparison

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  (A : Type (u + 1)) [CommRing A] (R : Sheaf J RingCat.{u + 1})
  (a : (Functor.const Cᵒᵖ).obj (RingCat.of A) ⟶ R.obj)

private noncomputable def restriction : SheafOfModules.{u + 1} R ⥤
    Sheaf J (ModuleCat.{u + 1} A) where
  obj M := by
    let P := (PresheafOfModules.restrictScalars a).obj M.val
    let F : Cᵒᵖ ⥤ ModuleCat.{u + 1} A :=
      { obj := P.obj
        map f := P.map f
        map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
        map_comp f g := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
    exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp J F
      (forget₂ (ModuleCat.{u + 1} A) AddCommGrpCat.{u + 1}) M.isSheaf⟩
  map φ := ⟨{
    app U := ((PresheafOfModules.restrictScalars a).map φ.val).app U
    naturality _ _ f := by
      ext x
      exact ConcreteCategory.congr_hom (φ.val.naturality f) x }⟩
  map_id M := by ext U x; rfl
  map_comp φ ψ := by ext U x; rfl

private noncomputable def restrictionFullyFaithful [Presheaf.IsLocallySurjective J a] :
    (restriction J A R a).FullyFaithful where
  preimage {M N} φ :=
    { val := (PresheafOfModules.restrictHomEquivOfIsLocallySurjective a N.isSheaf).symm
        { app := φ.hom.app
          naturality f := by ext x; exact ConcreteCategory.congr_hom (φ.hom.naturality f) x } }
  map_preimage φ := by ext U x; rfl
  preimage_map φ := by ext U x; rfl

variable [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
  [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} A)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective (ModuleCat.{u + 1} A)]

private noncomputable def constantPresheaf (M : ModuleCat.{u + 1} A) :
    PresheafOfModules.{u + 1} ((Functor.const Cᵒᵖ).obj (RingCat.of A)) where
  obj _ := M
  map _ := 𝟙 M

private noncomputable def constantComparisonHom (M : ModuleCat.{u + 1} A) :
    (constantSheaf J (ModuleCat.{u + 1} A)).obj M ⟶
      (restriction J A R a).obj
        ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M)) := by
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app (constantPresheaf A M)
  exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv _ _).symm
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }

omit [HasSheafify J AddCommGrpCat.{u + 1}] [HasSheafify J (ModuleCat.{u + 1} A)] in
private theorem constantComparisonHom_isIso (M : ModuleCat.{u + 1} A) :
    IsIso (constantComparisonHom J A R a M) := by
  let N := (restriction J A R a).obj
    ((PresheafOfModules.sheafification.{u + 1} a).obj (constantPresheaf A M))
  let η := (PresheafOfModules.sheafificationAdjunction.{u + 1} a).unit.app
    (constantPresheaf A M)
  let η' : (Functor.const Cᵒᵖ).obj M ⟶ N.obj :=
    { app U := η.app U
      naturality _ _ f := by ext x; exact ConcreteCategory.congr_hom (η.naturality f) x }
  have hηi : Presheaf.IsLocallyInjective J η' := by
    apply (Presheaf.isLocallyInjective_forget_iff _ _).mp
    change Presheaf.IsLocallyInjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hηs : Presheaf.IsLocallySurjective J η' := by
    apply (Presheaf.isLocallySurjective_iff_whisker_forget _ _).mpr
    change Presheaf.IsLocallySurjective J
      (Functor.whiskerRight (toSheafify J (constantPresheaf A M).presheaf)
        (CategoryTheory.forget AddCommGrpCat.{u + 1}))
    infer_instance
  have hf : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
      (constantComparisonHom J A R a M).hom = η' := by
    exact ((sheafificationAdjunction J (ModuleCat.{u + 1} A)).homEquiv
      ((Functor.const Cᵒᵖ).obj M) N).apply_symm_apply η'
  apply (Sheaf.isLocallyBijective_iff_isIso _).mp
  constructor
  · change Presheaf.IsLocallyInjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective_fac
      J η' hf
  · change Presheaf.IsLocallySurjective J (constantComparisonHom J A R a M).hom
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J hf

end ConstantScalarComparison

private theorem localConstancy_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    IsLocallyConstantProEtaleModuleSheaf T B F ↔
      IsLocallyConstantProEtaleFixedModuleSheaf T (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) := by
  let A := ULift.{u + 1, u} B
  let R := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing T B)
  have h (U : T.ProEt) :
      Presheaf.IsLocallyInjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) ∧
      Presheaf.IsLocallySurjective ((ProEt.topology T).over U)
        (Functor.whiskerLeft (Over.forget U).op (proEtaleModuleScalarUnit T B)) :=
    proEtaleConstantRingUnit_over_locallyBijective T B U
  constructor
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨E.mapIso e ≪≫
      (asIso (ConstantScalarComparison.constantComparisonHom
        ((ProEt.topology T).over (U i)) A (R.over (U i)) a M)).symm⟩⟩
  · rintro ⟨I, U, f, hf, he⟩
    refine ⟨I, U, f, hf, fun i ↦ ?_⟩
    obtain ⟨M, ⟨e⟩⟩ := he i
    let a := Functor.whiskerLeft (Over.forget (U i)).op (proEtaleModuleScalarUnit T B)
    have := (h (U i)).1
    have := (h (U i)).2
    let E := ConstantScalarComparison.restriction ((ProEt.topology T).over (U i))
      A (R.over (U i)) a
    have hc := ConstantScalarComparison.constantComparisonHom_isIso
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a M
    exact ⟨M, ⟨(ConstantScalarComparison.restrictionFullyFaithful
      ((ProEt.topology T).over (U i)) A (R.over (U i)) a).preimageIso
        (e ≪≫ asIso (ConstantScalarComparison.constantComparisonHom
          ((ProEt.topology T).over (U i)) A (R.over (U i)) a M))⟩⟩

private theorem finite_stalk_iff (T : Scheme.{u}) (B : Type u) [CommRing B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B))
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T) :
    Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) ↔
      Finite (proEtaleGeometricFixedModuleStalk x (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F)) := by
  let D := proEtaleGeometricStalkDiagram x ((proEtaleModuleRestriction T B).obj F)
  let e := CategoryTheory.preservesColimitIso
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1}) D
  constructor
  · intro h
    have : Finite (↑(Limits.colimit (D ⋙
        forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) AddCommGrpCat.{u + 1})) :
          Type (u + 1)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom)).symm
  · intro h
    have : Finite ((forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} B))
        AddCommGrpCat.{u + 1}).obj (Limits.colimit D)) := h
    exact Finite.of_equiv _
      (Equiv.ofBijective e.hom (ConcreteCategory.bijective_of_isIso e.hom))

private theorem finiteLocal_iff (T : Scheme.{u}) (B : Type u) [CommRing B] [Finite B]
    (F : proEtaleRingModules T (proEtaleConstantRing T B)) :
    ProEtale.IsFiniteLocallyConstant (ULift.{u + 1, u} B)
        ((proEtaleModuleRestriction T B).obj F) ↔
      IsLocallyConstantProEtaleModuleSheaf T B F ∧
        ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ T),
          Finite (proEtaleGeometricModuleStalk x (proEtaleConstantRing T B) F) := by
  constructor
  · intro h
    have hl := ProEtale.finiteModels_over (ULift.{u + 1, u} B) _ h
    refine ⟨(localConstancy_iff T B F).mpr ?_, fun Ω _ _ x ↦ ?_⟩
    · obtain ⟨I, U, f, hf, he⟩ := hl
      exact ⟨I, U, f, hf, fun i ↦ ⟨(he i).choose, (he i).choose_spec.2⟩⟩
    · exact (finite_stalk_iff T B F Ω x).mpr
        (ProEtale.finite_geometricStalk_of_finite_models (ULift.{u + 1, u} B) _ h Ω x)
  · rintro ⟨hl, hs⟩
    exact finite_models_of_fixed_lisse T (ULift.{u + 1, u} B) _
      ⟨(localConstancy_iff T B F).mp hl,
        fun Ω _ _ x ↦ (finite_stalk_iff T B F Ω x).mp (hs Ω x)⟩


/-- The canonical coefficient realization reflects the finite lisse condition.
Source: Stacks Project, Tag 00YV, fixed-module structures on a topos, and Tag 099Y.
(blueprint: new-lem-pur-intrinsic-lisse-fixed).

Proof: restriction of scalars along the constant-scalar unit is inverse to the canonical
realization. On every localized site, realization of a constant fixed module is the
simultaneous ring-and-module sheafification used in proEtaleConstantModuleSheafOver:
both are the sheafification of the same constant module presheaf with the same scalar
map. The unit and counit identify these constructions and commute with localization.
Apply the inverse equivalence to each trivialization in hM to obtain the identical cover
and fixed-module trivializations. On pointed neighbourhoods, the underlying additive
maps of the scalar-unit comparison commute with restriction. Their colimit identifies
the fixed-module stalk of the inverse realization with the intrinsic stalk after
restriction along the constant ring germ. This is precisely finiteCoefficientModuleStalkFunctor.
The identification is bijective, so hfinite transfers finiteness of every geometric stalk.
No conservativity of geometric stalks for arbitrary pro-etale sheaves is asserted.
Empty covers, the empty scheme and zero modules are included. -/
theorem proEtale_intrinsic_lisse_fixed (S : Scheme.{u})
    (Λ : Type u) [CommRing Λ] [Finite Λ]
    (M : proEtaleRingModules S (proEtaleConstantRing S Λ))
    (hM : IsLocallyConstantProEtaleModuleSheaf S Λ M)
    (hfinite : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ S),
      Finite ((finiteCoefficientModuleStalkFunctor y Λ).obj M)) :
    IsLisseProEtaleFixedModuleSheaf S (ULift.{u + 1, u} Λ)
      ((sfIntrinsicModuleEquivalence S Λ).inverse.obj M) := by
  let E := sfIntrinsicModuleEquivalence S Λ
  let R := proEtaleModuleRestriction S Λ
  let F := E.inverse.obj M
  let P := (ProEtale.finiteCoefficientModulePresheaf S.ProEt
    (ULift.{u + 1, u} Λ)).obj F.obj
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (ProEtale.finiteCoefficientIntrinsicScalarMap S Λ)
  let η : F ⟶ R.obj (E.functor.obj F) :=
    ⟨{ app U := (adj.unit.app P).app U
       naturality _ _ f := by
         ext x
         exact ConcreteCategory.congr_hom ((adj.unit.app P).naturality f) x }⟩
  have : IsIso η := by
    have : IsIso (adj.unit.app P) := by
      rw [← isIso_iff_of_reflects_iso _ (PresheafOfModules.toPresheaf _)]
      change IsIso (toSheafify (ProEt.topology S) P.presheaf)
      exact isIso_toSheafify (ProEt.topology S)
        ((sheafCompose (ProEt.topology S)
          (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ))
            AddCommGrpCat.{u + 1})).obj F).property
    have hη (U : S.ProEtᵒᵖ) : IsIso (η.hom.app U) := by
      have : IsIso ((PresheafOfModules.toPresheaf _).map (adj.unit.app P)) :=
        inferInstance
      have : IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U) :=
        inferInstance
      rw [← isIso_iff_of_reflects_iso _
        (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} Λ)) AddCommGrpCat.{u + 1})]
      change IsIso (((PresheafOfModules.toPresheaf _).map (adj.unit.app P)).app U)
      infer_instance
    rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
    change IsIso η.hom
    rw [NatTrans.isIso_iff_isIso_app]
    exact hη
  let e : F ≅ R.obj M := asIso η ≪≫ R.mapIso (E.counitIso.app M)
  have hr := (finiteLocal_iff S Λ M).2 ⟨hM, hfinite⟩
  have hf := ProEtale.isFiniteLocallyConstant_of_iso e.symm hr
  obtain ⟨I, U, f, hcover, hmodel⟩ := ProEtale.finiteModels_over
    (ULift.{u + 1, u} Λ) F hf
  refine ⟨⟨I, U, f, hcover, fun i ↦ ?_⟩, ?_⟩
  · obtain ⟨N, _, he⟩ := hmodel i
    exact ⟨N, he⟩
  · exact ProEtale.finite_geometricStalk_of_finite_models _ F hf

end AlgebraicGeometry.Scheme
