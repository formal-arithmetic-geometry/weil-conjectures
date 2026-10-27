/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R7
-/
module

public import Sheaf.CategoryTheory.ToposOpenScalarBasic
import Sheaf.CategoryTheory.ElementSiteDescent
import all Sheaf.CategoryTheory.ElementModulePresheafExtension
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Sites.CoverLifting

/-! # Invertibility of the actual element-site open unit -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.ToposOpenScalar
attribute [local instance 0] hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] hasSheafCompose_of_preservesLimitsOfSize
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (A : Sheaf J (Type u))

private theorem subterminal_sections (hA : IsSubterminal A) (U : Cᵒᵖ) :
    Subsingleton (A.obj.obj U) := by
  let e := ((sheafificationAdjunction J (Type u)).homEquiv
    (yoneda.obj U.unop) A).trans yonedaEquiv
  exact ⟨fun x y ↦ e.symm.injective (hA (e.symm x) (e.symm y))⟩

private theorem rawExtension_unit_isIso (B : Sheaf J RingCat.{u})
    (hA : IsSubterminal A) : IsIso (rawSumAdjunction B A).unit := by
  classical
  have hcomponent (M) : IsIso ((rawSumAdjunction B A).unit.app M) := by
    have hi : ∀ U, IsIso (((rawSumAdjunction B A).unit.app M).app U) := by
      intro U
      obtain ⟨⟨⟨U, s⟩⟩⟩ := U
      let := subterminal_sections A hA U
      let : DecidableEq (A.obj.obj U) := fun _ _ ↦ Classical.propDecidable _
      apply (ConcreteCategory.isIso_iff_bijective _).2
      change Function.Bijective
        (fun x ↦ ((rawSumAdjunction B A).unit.app M).app (elementObj A U s) x)
      have he : ((rawSumAdjunction B A).unit.app M).app (elementObj A U s) =
          ModuleCat.ofHom (DirectSum.lof (B.obj.obj U) (A.obj.obj U)
            (fun t ↦ (M.obj (elementObj A U t) : Type u)) s) := by
        ext x
        rw [← Adjunction.homEquiv_id]
        unfold rawSumAdjunction
        rw [Adjunction.adjunctionOfEquivLeft, Adjunction.mkOfHomEquiv_homEquiv]
        dsimp [sumHomEquiv, sumToRestriction]
        simp only [PresheafOfModules.id_app]
        dsimp [rawSumFunctor, Adjunction.leftAdjointOfEquiv]
        set_option backward.isDefEq.respectTransparency.types false in
          exact LinearMap.id_apply (R := B.obj.obj U)
            (M := DirectSum (A.obj.obj U) (fun t ↦ (M.obj (elementObj A U t) : Type u)))
            (DirectSum.lof (B.obj.obj U) (A.obj.obj U)
              (fun t ↦ (M.obj (elementObj A U t) : Type u)) s x)
      rw [he]
      change Function.Bijective (DirectSum.lof (B.obj.obj U) (A.obj.obj U)
        (fun t ↦ (M.obj (elementObj A U t) : Type u)) s)
      refine ⟨DirectSum.of_injective s, ?_⟩
      intro z
      induction z using DirectSum.induction_on with
      | zero => exact ⟨0, map_zero _⟩
      | of t x =>
        have ht : t = s := Subsingleton.elim _ _
        subst t
        exact ⟨x, rfl⟩
      | add x y hx hy =>
        obtain ⟨x, rfl⟩ := hx
        obtain ⟨y, rfl⟩ := hy
        exact ⟨x + y, map_add _ _ _⟩
  
    let := hi
    let e := PresheafOfModules.isoMk
      (fun U ↦ asIso (((rawSumAdjunction B A).unit.app M).app U))
      (by
        intro U V f
        exact ((rawSumAdjunction B A).unit.app M).naturality f)
    exact (show IsIso e.hom from inferInstance)
  have := hcomponent
  exact NatIso.isIso_of_isIso_app _

private def restrictionSheafificationUnit (B : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} B.obj) :
    (PresheafOfModules.pushforward (F := elementProjection A)
        (𝟙 (elementRing B A).obj)).obj P ⟶
      (PresheafOfModules.restrictScalars (𝟙 (elementRing B A).obj)).obj
        (((elementModulePullback B A).obj
          ((PresheafOfModules.sheafification.{u, u, u, u} (𝟙 B.obj)).obj P)).val) where
  app U := ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
    (𝟙 B.obj)).unit.app P).app ((elementProjection A).op.obj U)
  naturality := by
    intro U V f
    ext m
    exact PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u} (𝟙 B.obj)).unit.app P)
      ((elementProjection A).op.map f) m

private def restrictionSheafificationMap (B : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} B.obj) :
    (PresheafOfModules.sheafification.{u, u, u, u} (𝟙 (elementRing B A).obj)).obj
        ((PresheafOfModules.pushforward (F := elementProjection A)
          (𝟙 (elementRing B A).obj)).obj P) ⟶
      (elementModulePullback B A).obj
        ((PresheafOfModules.sheafification.{u, u, u, u} (𝟙 B.obj)).obj P) :=
  (PresheafOfModules.sheafificationHomEquiv.{u, u, u, u}
    (𝟙 (elementRing B A).obj)).symm (restrictionSheafificationUnit A B P)

set_option backward.isDefEq.respectTransparency true in
private theorem restrictionSheafificationMap_unit (B : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} B.obj) (U : A.obj.Elementsᵒᵖᵒᵖ)
    (x : P.obj ((elementProjection A).op.obj U)) :
    (restrictionSheafificationMap A B P).val.app U
        (((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
          (𝟙 (elementRing B A).obj)).unit.app
          ((PresheafOfModules.pushforward (F := elementProjection A)
            (𝟙 (elementRing B A).obj)).obj P)).app U x) =
      ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u} (𝟙 B.obj)).unit.app P).app
        ((elementProjection A).op.obj U) x := by
  have h := (PresheafOfModules.sheafificationHomEquiv.{u, u, u, u}
    (𝟙 (elementRing B A).obj)
    (P := (PresheafOfModules.pushforward (F := elementProjection A)
      (𝟙 (elementRing B A).obj)).obj P)
    (F := (elementModulePullback B A).obj
      ((PresheafOfModules.sheafification.{u, u, u, u} (𝟙 B.obj)).obj P))).apply_symm_apply
      (restrictionSheafificationUnit A B P)
  exact congrArg (fun g ↦ g.app U x) h

private theorem restrictionSheafificationMap_toSheaf (B : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} B.obj)
    [Functor.IsCocontinuous (elementProjection A) (elementTopology A) J] :
    (SheafOfModules.toSheaf _).map (restrictionSheafificationMap A B P) =
      ((elementProjection A).pushforwardContinuousSheafificationCompatibility
        AddCommGrpCat.{u} (elementTopology A) J).hom.app P.presheaf := by
  let F := elementProjection A
  let _ := (element_site_descent A).2.1
  let e := F.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u} (elementTopology A) J
  have he : (SheafOfModules.toSheaf _).map (restrictionSheafificationMap A B P) =
      e.hom.app P.presheaf := by
    unfold restrictionSheafificationMap
    rw [PresheafOfModules.toSheaf_map_sheafificationHomEquiv_symm
      (𝟙 (elementRing B A).obj)]
    apply ((sheafificationAdjunction (elementTopology A) AddCommGrpCat.{u}).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    change Functor.whiskerLeft F.op (toSheafify J P.presheaf) =
      toSheafify (elementTopology A) (F.op ⋙ P.presheaf) ≫
        (e.hom.app P.presheaf).hom
    exact (F.toSheafify_pullbackSheafificationCompatibility
      AddCommGrpCat.{u} (elementTopology A) J P.presheaf).symm
  exact he

private theorem restrictionSheafificationMap_isIso (B : Sheaf J RingCat.{u})
    (P : PresheafOfModules.{u} B.obj) : IsIso (restrictionSheafificationMap A B P) := by
  let F := elementProjection A
  let _ := (element_site_descent A).2.1
  let e := F.pushforwardContinuousSheafificationCompatibility
    AddCommGrpCat.{u} (elementTopology A) J
  have : IsIso ((SheafOfModules.toSheaf _).map (restrictionSheafificationMap A B P)) := by
    rw [restrictionSheafificationMap_toSheaf]
    infer_instance
  exact isIso_of_reflects_iso (restrictionSheafificationMap A B P) (SheafOfModules.toSheaf _)

@[irreducible] private def restrictionSheafificationIso (B : Sheaf J RingCat.{u}) :
    PresheafOfModules.pushforward (F := elementProjection A) (𝟙 (elementRing B A).obj) ⋙
        PresheafOfModules.sheafification.{u, u, u, u} (𝟙 (elementRing B A).obj) ≅
      PresheafOfModules.sheafification.{u, u, u, u} (𝟙 B.obj) ⋙
        elementModulePullback B A := by
  set_option backward.isDefEq.respectTransparency true in
    have (P : PresheafOfModules.{u} B.obj) := restrictionSheafificationMap_isIso A B P
    let := (element_site_descent A).2.1
    refine NatIso.ofComponents (fun P ↦ asIso (restrictionSheafificationMap A B P)) ?_
    intro P N g
    apply (SheafOfModules.toSheaf _).map_injective
    rw [Functor.map_comp, Functor.map_comp]
    change _ ≫ (SheafOfModules.toSheaf _).map (restrictionSheafificationMap A B N) =
      (SheafOfModules.toSheaf _).map (restrictionSheafificationMap A B P) ≫ _
    rw [restrictionSheafificationMap_toSheaf, restrictionSheafificationMap_toSheaf]
    exact ((elementProjection A).pushforwardContinuousSheafificationCompatibility
      AddCommGrpCat.{u} (elementTopology A) J).hom.naturality
        ((PresheafOfModules.toPresheaf B.obj).map g)

private theorem ordinaryOpenUnit_isIso (B : Sheaf J RingCat.{u})
    (hA : IsSubterminal A) :
    IsIso (SheafOfModules.pullbackPushforwardAdjunction
      (F := elementProjection A) (𝟙 (elementRing B A))).unit := by
  have := rawExtension_unit_isIso A B hA
  let e := SheafOfModules.pullbackIso (F := elementProjection A) (𝟙 (elementRing B A))
  let k := (rawSumAdjunction B A).leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction
      (F := elementProjection A) (𝟙 (elementRing B A).obj))
  let es : elementModuleExtension B A ≅
      SheafOfModules.forget (elementRing B A) ⋙ rawSumFunctor B A ⋙
        PresheafOfModules.sheafification (𝟙 B.obj) :=
    e ≪≫ Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight k.symm _)
  let F := SheafOfModules.forget (elementRing B A)
  let T := PresheafOfModules.sheafification.{u, u, u, u} (𝟙 (elementRing B A).obj)
  let j : elementModuleExtension B A ⋙ elementModulePullback B A ≅ 𝟭 _ :=
    Functor.isoWhiskerRight es _ ≪≫
    Functor.associator F (rawSumFunctor B A ⋙
      PresheafOfModules.sheafification (𝟙 B.obj)) (elementModulePullback B A) ≪≫
    Functor.isoWhiskerLeft F
      ((Functor.associator (rawSumFunctor B A)
        (PresheafOfModules.sheafification (𝟙 B.obj)) (elementModulePullback B A)) ≪≫
        Functor.isoWhiskerLeft (rawSumFunctor B A) (restrictionSheafificationIso A B).symm ≪≫
        (Functor.associator (rawSumFunctor B A) _ T).symm ≪≫
        Functor.isoWhiskerRight (asIso (rawSumAdjunction B A).unit).symm T ≪≫
        Functor.leftUnitor T) ≪≫
    asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (elementRing B A).obj)).counit
  exact Adjunction.isIso_unit_of_iso _ j


variable (R : Sheaf J CommRingCat.{u})
  [HasDerivedCategory.{w}
    (ringedSiteModules.{u} (derivedChangeRingIndependentCoefficients J R))]
  [HasDerivedCategory.{w} (ringedSiteModules.{u}
    (derivedChangeRingIndependentCoefficients (elementTopology A) (presentationElementRing R A)))]
  [(extension R A).Additive] [(restriction R A).Additive]
  [PreservesFiniteLimits (extension R A)] [PreservesFiniteColimits (extension R A)]
  [PreservesFiniteLimits (restriction R A)] [PreservesFiniteColimits (restriction R A)]

/-- The actual open extension/restriction unit is invertible after exact localization.
Source: Stacks 04IE and 0E8I (blueprint: lem-pur-topos-open-derived-unit-is-iso).

Proof: By Yoneda, subterminality makes each set of sections a subsingleton. At an
object of the element site it is inhabited, so the direct-sum extension unit is an
isomorphism onto its unique summand. Restriction commutes with sheafification, hence
this gives an isomorphism from extension followed by restriction to the identity.
The actual adjunction unit is consequently invertible. Its cochain unit is invertible
in every degree, and the exact localization formula expresses its derived unit as
its quotient image followed by the two factorization isomorphisms. Every derived
object is isomorphic to such a quotient object. -/
theorem toposOpenDerivedUnit_isIso
    (hA : IsSubterminal A) :
    IsIso (OpenTensorNormalization.exactDerivedAdjunction (normalizedAdjunction R A)).unit := by
  have hu : IsIso (normalizedAdjunction R A).unit :=
    ordinaryOpenUnit_isIso A (derivedChangeRingIndependentCoefficients J R) hA
  let d := OpenTensorNormalization.exactDerivedAdjunction (normalizedAdjunction R A)
  have hQ (P : CochainComplex (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients (elementTopology A)
        (presentationElementRing R A))) ℤ) : IsIso (d.unit.app (DerivedCategory.Q.obj P)) := by
    have hi (n : ℤ) : IsIso
        ((((normalizedAdjunction R A).mapHomologicalComplex (.up ℤ)).unit.app P).f n) :=
      inferInstanceAs (IsIso ((normalizedAdjunction R A).unit.app (P.X n)))
    have := HomologicalComplex.Hom.isIso_of_components
      (((normalizedAdjunction R A).mapHomologicalComplex (.up ℤ)).unit.app P)
    have he : d.unit.app (DerivedCategory.Q.obj P) =
        DerivedCategory.Q.map (((normalizedAdjunction R A).mapHomologicalComplex
          (.up ℤ)).unit.app P) ≫
        (restriction R A).mapDerivedCategoryFactors.inv.app _ ≫
          (restriction R A).mapDerivedCategory.map
            ((extension R A).mapDerivedCategoryFactors.inv.app P) := by
      simp only [d, OpenTensorNormalization.exactDerivedAdjunction,
        Adjunction.localization_unit_app]
      rfl
    rw [he]
    infer_instance
  have (M : DerivedCategory (ringedSiteModules.{u}
      (derivedChangeRingIndependentCoefficients (elementTopology A)
        (presentationElementRing R A)))) : IsIso (d.unit.app M) :=
    (NatTrans.isIso_app_iff_of_iso d.unit
      (DerivedCategory.Q.objObjPreimageIso M)).mp (hQ _)
  exact NatIso.isIso_of_isIso_app _

end SheafOfModules.ToposOpenScalar
