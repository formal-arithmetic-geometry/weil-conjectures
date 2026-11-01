/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProEtaleRootsOfUnityInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistConstructions
public import WeilConjectures.AlgebraicGeometry.StrictConstantTowerOperations
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperationsTransport
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.AlgebraicGeometry.TateInverseLimitBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.PurTwistSheaves
public import WeilConjectures.AlgebraicGeometry.SfIntegralReductionTower
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Proetale.Sheafification
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison

/-! # Cartesian coefficients and Tate twists

md`
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u u₁ v₁ u₂ v₂ uI vI uJ vJ

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj ChangeOfRings

section ModuleComparisons

universe w₁ vM₁ w₂ vM₂
variable {C : Type w₁} [Category.{vM₁} C] [MonoidalCategory C]
  {D : Type w₂} [Category.{vM₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R]
open CategoryTheory.Limits

end ModuleComparisons

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory

-- Keep the scalar-extension object abstract; its coequalizer equations are the API.
attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
  AlgebraicGeometry.ProEtale.CondensedRing.pullIso

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Fixed-universe presentations cache the categorical instance arguments.
private abbrev AbSheaf (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}
private instance proEtSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private instance abelianSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} := inferInstance
private instance abelianWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} := inferInstance
private instance ringSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) RingCat.{u + 1} := inferInstance
private instance ringWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) RingCat.{u + 1} := inferInstance
private instance commRingSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u + 1} T
private instance commRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} := inferInstance
private instance typeSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) (Type (u + 1)) := inferInstance
private instance typeWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) (Type (u + 1)) := inferInstance

private instance abelianForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget AddCommGrpCat.{u + 1}) := inferInstance
private instance ringForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget RingCat.{u + 1}) := inferInstance
private instance commRingForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget CommRingCat.{u + 1}) := inferInstance
private instance commRingToRingSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance

private instance integralSystem_hasLimit (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : HasLimit (spIntegralTwistSystem T ℓ E) :=
  inferInstance

private instance integralSystem_forget_preservesLimit
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PreservesLimit (spIntegralTwistSystem T ℓ E)
      (Mod.forget (C := AbSheaf T)
        (D := AbSheaf T)
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) T)) :=
  inferInstance

private instance pullback_forget_kan
    {D : Type (u + 2)} [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : D ⥤ Type (u + 1)) [PreservesFilteredColimitsOfSize.{u + 1, u + 1} G]
    (P : Y.ProEtᵒᵖ ⥤ D) :
    G.PreservesPointwiseLeftKanExtension P (Scheme.proEtaleBaseChange f).op := by
  let U := Scheme.proEtaleBaseChange f
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits _
  intro W
  have : IsFiltered (CostructuredArrow U.op W) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
  have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
    have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
    have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
    infer_instance
  exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W

private def abelianPullbackForgetIso :
    upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1})

private theorem abelianPullbackForgetIso_unit
    (R : AbSheaf Y)
    (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) :
    ((abelianPullbackForgetIso f).hom.app R).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app R).hom.app V a) =
      ((setPullbackAdjunction f).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj R)).hom.app
          V a := by
  exact congrArg (fun q ↦ q.hom.app V a)
    (sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1}) R)

private def ringPullbackForgetIso :
    Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget CommRingCat.{u + 1})

private theorem ringPullbackForgetIso_unit
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) :
    ((ringPullbackForgetIso f).hom.app R).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app V a) =
      ((setPullbackAdjunction f).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1})).obj R)).hom.app
          V a := by
  exact congrArg (fun q ↦ q.hom.app V a)
    (sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (forget CommRingCat.{u + 1}) R)

private def noncommPullbackForgetIso :
    Scheme.proEtaleSheafInverseImage f RingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget RingCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget RingCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget RingCat.{u + 1})

attribute [local irreducible] abelianPullbackForgetIso ringPullbackForgetIso
  noncommPullbackForgetIso
  condensedPushforwardHom

private theorem sectionRingPullbackIso_existsUnique
    (RY : AbSheaf Y)
    (RX : AbSheaf X)
    [MonObj RY] [IsCommMonObj RY] [MonObj RX] [IsCommMonObj RX]
    (α : (upperStar AddCommGrpCat.{u + 1} f).obj RY ⟶ RX) [IsIso α]
    (eta : RY ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj RX)
    (heta : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
      (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) α).hom.app
        V a = eta.hom.app V a)
    (β : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) RY ⟶
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX))
    (hβ : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V), β.hom.app V a = eta.hom.app V a) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) RY) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX,
      ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = eta.hom.app V a := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) RY
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) RX
  let c := ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).symm β
  have hc : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) c).hom.app V a =
        eta.hom.app V a := by
    intro V a
    change (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S)
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).symm β)).hom.app
        V a = _
    rw [Equiv.apply_symm_apply]
    exact hβ V a
  clear_value c
  have hi : IsIso c := by
    let U := sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})
    let UR := sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})
    let e := ((ringPullbackForgetIso f).app R).symm
    let d := (abelianPullbackForgetIso f).app RY
    have heunit (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V) :
        e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app
              V a) = (((setPullbackAdjunction f).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1})).obj R)).hom.app
            V a) := by
      exact ringPullbackForgetIso_unit f R V a
    have hdunit (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V) :
        d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
              RY).hom.app V a) = (((setPullbackAdjunction f).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj RY)).hom.app
            V a) := by
      exact abelianPullbackForgetIso_unit f RY V a
    clear_value e d
    have he : e.hom ≫ UR.map c =
        d.inv ≫ U.map α := by
      apply ((setPullbackAdjunction f).homEquiv _ _).injective
      ext V a
      change (UR.map c).hom.app _
          (e.hom.hom.app _ (((setPullbackAdjunction f).unit.app _).hom.app V a)) = _
      have hr₀ := heunit V a
      have hr := congrArg (fun z ↦ e.hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V) z) hr₀
      have hidr : ∀ x, e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x := by
        intro x
        exact congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
          e.inv_hom_id
      change e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app
            V a)) = _ at hr
      rw [hidr] at hr
      have hr := hr.symm
      erw [hr]
      change (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) c).hom.app
        V a = _
      rw [hc V a]
      have hd := hdunit V a
      have hd' := congrArg (fun z ↦ d.inv.hom.app _ z) hd
      have hid : ∀ x, d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x := by
        intro x
        exact congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
          d.hom_inv_id
      change d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
            RY).hom.app V a)) = _ at hd'
      rw [hid] at hd'
      rw [Adjunction.homEquiv_unit]
      change eta.hom.app V a =
        α.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((setPullbackAdjunction f).unit.app _).hom.app V a))
      rw [← hd']
      exact (heta V a).symm
    have : IsIso (e.hom ≫ UR.map c) := by
      rw [he]
      infer_instance
    have : IsIso (UR.map c) := IsIso.of_isIso_comp_left e.hom _
    exact isIso_of_reflects_iso c
      (sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1}))
  have := hi
  refine ⟨asIso c, hc, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).injective
  ext V a
  exact (hc' V a).trans (hc V a).symm

private theorem abelianAdjunct_eq
    (R : AbSheaf Y)
    (S : AbSheaf X)
    (g : (upperStar AddCommGrpCat.{u + 1} f).obj R ⟶ S) :
    ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) g =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app R ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map g := by
  rw [Adjunction.homEquiv_unit]
  rfl

private def liftRingSheafMap
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (φ : (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    R ⟶ (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S :=
  ⟨{ app := fun V ↦
       (show R.obj.obj V ⟶ S.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V) from
         ConcreteCategory.ofHom (C := CommRingCat) (φ.hom.app V).hom)
     naturality := by
       intro V W g
       ext x
       exact ConcreteCategory.congr_hom (φ.hom.naturality g) x }⟩

private theorem sectionRingPullbackIso_ofMonHom
    (RY : AbSheaf Y)
    (RX : AbSheaf X)
    [MonObj RY] [IsCommMonObj RY] [MonObj RX] [IsCommMonObj RX]
    (α : (upperStar AddCommGrpCat.{u + 1} f).obj RY ⟶ RX) [IsIso α]
    (eta : RY ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj RX) [IsMonHom eta]
    (heta : ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) α = eta) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) RY) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX,
      ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = eta.hom.app V a := by
  obtain ⟨φ, hφ, _⟩ := InternalModuleOperations.sectionRingMap_existsUnique
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
    RX RY eta
  exact sectionRingPullbackIso_existsUnique f RY RX α eta
    (fun V a ↦ congrArg (fun q ↦ q.hom.app V a) heta) (liftRingSheafMap f _ _ φ) hφ

/-- The ring-sheaf encoding of alpha is uniquely fixed by its abelian adjunct.
Source: blueprint coefficient compatibility, lem-sfb-alpha-iso
(blueprint: det-prop-sfb-cartesian-coefficients-twists).
Proof: reconstruct section rings from the internal multiplication. The coefficient
adjunct is a ring homomorphism since condensedPullbackHom is monoidal. Lift the
abelian adjunction to ring objects. Its adjunct determines the map uniquely, and
alpha is invertible by lem-sfb-alpha-iso; forgetting reflects isomorphisms. -/
theorem spCoefficientIso_existsUnique
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
          (condensedRingObj Λ Y)) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (condensedRingObj Λ X),
      ∀ (V : Y.ProEtᵒᵖ) (a : (condensedRingObj Λ Y).obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = (condensedPushforwardHom Λ f).hom.app V a := by
  apply sectionRingPullbackIso_ofMonHom f (condensedRingObj Λ Y)
    (condensedRingObj Λ X) (condensedPullbackHom Λ f) (condensedPushforwardHom Λ f)
  exact (abelianAdjunct_eq f _ _ _).trans (unitAlgHom_comp_map_condensedPullbackHom Λ f)

attribute [local irreducible] profinitePointModuleForgetPullbackIso

section SignedComparisonStatement
attribute [local irreducible] Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction
end SignedComparisonStatement

section SignedPullbackProof

attribute [local irreducible] Scheme.proEtaleModuleInverseImage
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  SheafOfModules.siteSheafTensorRight

end SignedPullbackProof

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
attribute [local irreducible] Scheme.proEtaleModuleInverseImage
end

section

variable (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
include T
private theorem zmodModule_normalized
    (M : SheafOfModules.{u + 1} (constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N)) :
    IsConstantZModSheafModuleStructure.{u + 1, u, u + 1} (Scheme.ProEt.topology T) N
      ((SheafOfModules.toSheaf.{u + 1} _).obj M)
      (fun V ↦ (M.val.obj V).isModule) := by
  constructor
  · intro V z x
    let := (M.val.obj V).isModule
    change @SMul.smul
      ((constantZModRingSheaf (Scheme.ProEt.topology T) N).obj.obj V)
      (M.val.obj V) (M.val.obj V).isModule.toSMul
      (((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} (ZMod N))))).app V).hom
          (z : ULift.{u + 1} (ZMod N))) x = z • x
    rw [map_intCast]
    exact Int.cast_smul_eq_zsmul
      ((constantZModRingSheaf (Scheme.ProEt.topology T) N).obj.obj V) z (show M.val.obj V from x)
  · intro V W a r x
    exact PresheafOfModules.map_smul M.val a r x
include hN
private def zmodModuleHom
    (M M' : SheafOfModules.{u + 1}
      (constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N))
    (a : (SheafOfModules.toSheaf.{u + 1} _).obj M ⟶ (SheafOfModules.toSheaf.{u + 1} _).obj M') :
    M ⟶ M' :=
  ⟨PresheafOfModules.homMk a.hom
    (torsionSheaf_hom_linear (Scheme.ProEt.topology T) N hN _ _
      (constantZModModuleSheaf_nsmul (Scheme.ProEt.topology T) N hN M)
      (constantZModModuleSheaf_nsmul (Scheme.ProEt.topology T) N hN M') a _ _
      (zmodModule_normalized T N M) (zmodModule_normalized T N M'))⟩

private def finiteRingModuleHom
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1})
    (e : R ≅ constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N)
    (M M' : SheafOfModules.{u + 1} R)
    (a : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj M') : M ⟶ M' := by
  let P := (SheafOfModules.restrictScalars e.inv).obj M
  let Q := (SheafOfModules.restrictScalars e.inv).obj M'
  let b := zmodModuleHom T N hN P Q a
  refine ⟨PresheafOfModules.homMk a.hom ?_⟩
  intro V r x
  let := (M.val.obj V).isModule
  let := (M'.val.obj V).isModule
  have h := ((b.val.app V).hom.map_smul (e.hom.hom.app V r) x)
  change a.hom.app V (e.inv.hom.app V (e.hom.hom.app V r) • x) =
    e.inv.hom.app V (e.hom.hom.app V r) • (show M'.val.obj V from a.hom.app V x) at h
  have he : e.inv.hom.app V (e.hom.hom.app V r) = r :=
    congrArg (fun k ↦ k.hom.app V r) e.hom_inv_id
  rw [he] at h
  exact h

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
private abbrev restr (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map p)
private abbrev tens (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p M
private abbrev tensorUnit' (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) : M ⟶ (restr T p).obj (tens T p M) :=
  Scheme.tensorHomEquiv T p M (tens T p M) (𝟙 _)
variable
    (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (pY : RY ⟶ SY) (pX : RX ⟶ SX)
    (hsq : pY ≫ Scheme.proEtaleRingDirectImageMap f SY SX cS =
      Scheme.proEtaleRingDirectImageMap f RY RX cR ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map pX)
private def directScalarIso'
    (H : Scheme.proEtaleRingModules X SX) :
    (restr Y pY).obj ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H) ≅
      (Scheme.proEtaleRingModuleDirectImage f RY RX cR).obj ((restr X pX).obj H) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ LinearEquiv.toModuleIso
      (X₁ := (((restr Y pY).obj
        ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H)).val.obj V))
      (X₂ := (((Scheme.proEtaleRingModuleDirectImage f RY RX cR).obj
        ((restr X pX).obj H)).val.obj V))
      { __ := AddEquiv.refl _
        map_smul' := fun r m ↦ by
          change @SMul.smul (SX.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul
            ((Scheme.proEtaleRingDirectImageMap f SY SX cS).hom.app V
              (pY.hom.app V r)) (show H.val.obj _ from m) =
            @SMul.smul (SX.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul
              (pX.hom.app _ ((Scheme.proEtaleRingDirectImageMap f RY RX cR).hom.app V r))
                (show H.val.obj _ from m)
          exact congrArg (fun z ↦ @SMul.smul _ (H.val.obj
            ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul z m)
            (congrArg (fun k ↦ k.hom.app V r) hsq) })
      (by intro V W a; ext m; rfl))
private def tensorPullbackHomEquiv'
    (M : Scheme.proEtaleRingModules Y RY) (H : Scheme.proEtaleRingModules X SX) :
    ((Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ H) ≃
      ((Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ (restr X pX).obj H) :=
  ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).homEquiv (tens Y pY M) H).trans
    ((Scheme.tensorHomEquiv Y pY M
      ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H)).trans
      ((Iso.homCongr (Iso.refl M) (directScalarIso' f RY SY RX SX cR cS pY pX hsq H)).trans
        ((Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv M
          ((restr X pX).obj H)).symm))
attribute [local irreducible] tensorPullbackHomEquiv' directScalarIso'

private def tensorMap'
    (M : Scheme.proEtaleRingModules Y RY) (N : Scheme.proEtaleRingModules X RX)
    (c : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ N) :
    (Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ tens X pX N :=
  (tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M (tens X pX N)).symm
    (c ≫ tensorUnit' X pX N)
attribute [local irreducible] tensorMap'

end

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
private def rootModuleDirect (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    Scheme.purTwistRootsModule Y ℓ r ⟶
      (Scheme.proEtaleRingModuleDirectImage f
        (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
        (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)).obj
          (Scheme.purTwistRootsModule X ℓ r) :=
  finiteRingModuleHom Y (ℓ ^ (r + 1)) (pow_pos (Fact.out : ℓ.Prime).pos _)
    (Scheme.purTwistRing Y (Scheme.purTwistFiniteRing Y ℓ r))
    (Scheme.purTwistFiniteRingIso Y ℓ r) _ _
    (Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1)))

attribute [local irreducible] rootModuleDirect tensorMap' directScalarIso' tensorPullbackHomEquiv'

section
end

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] spIntegersMap spEllMap spIntegralTwistMap
  spRationalTwistMap
end

attribute [local irreducible] spRationalTwistMap spIntegralTwistMap spEllMap
  spIntegersMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  InternalModuleOperations.lowerComparison InternalModuleOperations.coefficientMap
end

attribute [local irreducible] spIntegralTwist
set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence
  InternalAbelianSheafModule.sectionRingSheaf
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

end AlgebraicGeometry.ProEtale
