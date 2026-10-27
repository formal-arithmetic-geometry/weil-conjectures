/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedTopoiTensorComparisonData
public import Sheaf.CategoryTheory.AlgebraicInverseImage
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Monoidal.Functor
import all Sheaf.SecSmoothPurity.CochainInverseComparison
import all Sheaf.Paper.StrictPerfectRingedPullbackModel
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Sheaf.Paper.ScalarExtensionBinaryCoherence
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # The tensor comparison is the specified adjunction mate

Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL.
(blueprint: lem-pd-ringed-tensor-adjunction-mate).
-/

@[expose] public section

universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace SheafOfModules
set_option autoImplicit false
set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency true
open scoped ChangeOfRings
attribute [local instance 12000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
attribute [local instance 11000] CategoryTheory.hasSheafComposeEssentiallySmallSite
set_option backward.isDefEq.respectTransparency.types false

-- Fix the coefficient functors before instance search enters small-model transport.
private theorem mateRingCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) := by infer_instance
private theorem mateAddCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{u}) := by infer_instance
private theorem mateRingSetCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (CategoryTheory.forget RingCat.{u}) := by infer_instance
private theorem mateCommRingSetCompose {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u}) := by infer_instance
attribute [local instance 20000] mateRingCompose mateAddCompose
  mateRingSetCompose mateCommRingSetCompose

private theorem mateWeakSheafify {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    HasWeakSheafify J AddCommGrpCat.{u} := by infer_instance
private theorem mateLocalEquivalences {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] (J : GrothendieckTopology E) :
    J.WEqualsLocallyBijective AddCommGrpCat.{u} := by infer_instance
attribute [local instance 20000] mateWeakSheafify mateLocalEquivalences

section AbstractMate
variable {A : Type*} {B : Type*} [Category A] [Category B]
  [MonoidalCategory A] [MonoidalCategory B]
  {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) [G.LaxMonoidal]

private theorem tensorMate_eq (X Y : A) (f : F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (h : adj.unit.app (X ⊗ Y) ≫ G.map f =
      (adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ Functor.LaxMonoidal.μ G _ _) :
    adj.leftAdjointOplaxMonoidal.δ X Y = f := by
  apply (adj.homEquiv _ _).injective
  change (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact h.symm

private theorem tensorMate_natural
    (e : ∀ X Y : A, F.obj (X ⊗ Y) ≅ F.obj X ⊗ F.obj Y)
    (he : ∀ X Y, adj.leftAdjointOplaxMonoidal.δ X Y = (e X Y).hom)
    {X X' Y Y' : A} (f : X ⟶ X') (g : Y ⟶ Y') :
    F.map (f ⊗ₘ g) ≫ (e X' Y').hom =
      (e X Y).hom ≫ (F.map f ⊗ₘ F.map g) := by
  let := adj.leftAdjointOplaxMonoidal
  rw [← he, ← he]
  exact (Functor.OplaxMonoidal.δ_natural F f g).symm

private theorem unitMate_eq (f : F.obj (𝟙_ A) ⟶ 𝟙_ B)
    (h : adj.unit.app (𝟙_ A) ≫ G.map f = Functor.LaxMonoidal.ε G) :
    f = adj.leftAdjointOplaxMonoidal.η := by
  apply (adj.homEquiv _ _).injective
  change (adj.homEquiv _ _) f = (adj.homEquiv _ _) ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact h

end AbstractMate

namespace RingedMate
attribute [local irreducible] monoidalCategory

private abbrev base {E : Type uC} [Category.{vC} E] [EssentiallySmall.{u} E]
    {J : GrothendieckTopology E} (A : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A

private noncomputable abbrev sets {E : Type uC} [Category.{vC} E]
    [EssentiallySmall.{u} E] {J : GrothendieckTopology E} (A : Sheaf J CommRingCat.{u}) :=
  toSheaf (base A) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

section Scalar
variable {E : Type uC} [Category.{vC} E] [EssentiallySmall.{u} E]
  {J : GrothendieckTopology E} {A B : Sheaf J CommRingCat.{u}} (α : A ⟶ B)

private noncomputable def extension : SheafOfModules.{u} (base A) ⥤
    SheafOfModules.{u} (base B) where
  obj M := changeOfRings.{vC, uC, u} α M
  map {M N} f := changeOfRingsHom.{vC, uC, u} α M f
  map_id M := by
    exact scalarExtension_map_id α M
  map_comp f g := by
    exact scalarExtension_map_comp α f g

private noncomputable def tensorPresentation (A : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (base A)) :
    (monoidalCategory A).tensorObj M N ≅ (siteSheafTensorRight N).obj M :=
  tensorObjIsoSheafification M N ≪≫
    (PresheafOfModules.sheafification.{u} (R := base A) (𝟙 (base A).obj)).mapIso
      ((siteTensorRightIso A N.val).app M.val).symm

private theorem tensorPresentation_pure (A : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (base A)) (W : Eᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    (tensorPresentation A M N).hom.val.app W (ringedComparisonPure A M N W m n) =
      siteSheafTensorTmul M N W m n := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u} (R := base A) (𝟙 (base A).obj)
  let e := (siteTensorRightIso A N.val).app M.val
  have hc := congrArg (fun f ↦ f.val.app W
    ((adj.unit.app (M.val ⊗ N.val)).app W (m ⊗ₜ[A.obj.obj W] n)))
    (tensorObjIsoSheafification M N).inv_hom_id
  change (tensorObjIsoSheafification M N).hom.val.app W
    ((tensorObjIsoSheafification M N).inv.val.app W
      ((adj.unit.app (M.val ⊗ N.val)).app W (m ⊗ₜ[A.obj.obj W] n))) = _ at hc
  have hn := congrArg (fun f ↦ f.app W (m ⊗ₜ[A.obj.obj W] n))
    (adj.unit.naturality e.inv)
  change (((PresheafOfModules.sheafification.{u} (R := base A) (𝟙 (base A).obj)).map
    e.inv).val.app W)
    ((tensorObjIsoSheafification M N).hom.val.app W
      ((tensorObjIsoSheafification M N).inv.val.app W
        ((adj.unit.app (M.val ⊗ N.val)).app W (m ⊗ₜ[A.obj.obj W] n)))) = _
  rw [hc]
  exact hn.symm

private theorem tensorPresentation_inv_pure (A : Sheaf J CommRingCat.{u})
    (M N : SheafOfModules.{u} (base A)) (W : Eᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    (tensorPresentation A M N).inv.val.app W (siteSheafTensorTmul M N W m n) =
      ringedComparisonPure A M N W m n := by
  have h := congrArg ((tensorPresentation A M N).inv.val.app W)
    (tensorPresentation_pure A M N W m n)
  exact h.symm.trans (congrArg (fun f ↦ f.val.app W
    (ringedComparisonPure A M N W m n)) (tensorPresentation A M N).hom_inv_id)

private noncomputable def scalarComparison (M N : SheafOfModules.{u} (base A)) :
    changeOfRings.{vC, uC, u} α ((monoidalCategory A).tensorObj M N) ≅
      (monoidalCategory B).tensorObj (changeOfRings.{vC, uC, u} α M) (changeOfRings.{vC, uC, u} α
        N) :=
  (extension (J := J) (A := A) (B := B) α).mapIso (tensorPresentation A M N) ≪≫
    scalarTensorBinaryIso (R := A) (S := B) α M N ≪≫
      (tensorPresentation B (changeOfRings.{vC, uC, u} α M) (changeOfRings.{vC, uC, u} α N)).symm

private theorem scalarMap_tmul (M N : SheafOfModules.{u} (base A)) (f : M ⟶ N)
    (W : Eᵒᵖ) (s : B.obj.obj W) (m : M.val.obj W) :
    (changeOfRingsHom.{vC, uC, u} α M f).val.app W
      (ringedComparisonScalarSection α M W s m) =
      ringedComparisonScalarSection α N W s (f.val.app W m) := by
  exact scalarExtension_map_tmul.{uC, vC, u, u} α f W s m


private theorem scalarComparison_pure (M N : SheafOfModules.{u} (base A))
    (W : Eᵒᵖ) (s : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    (scalarComparison α M N).hom.val.app W
      (ringedComparisonScalarSection α _ W s (ringedComparisonPure A M N W m n)) =
    ringedComparisonPure B _ _ W
      (ringedComparisonScalarSection α M W s m)
      (ringedComparisonScalarSection α N W 1 n) := by
  change (tensorPresentation B _ _).inv.val.app W
    ((scalarTensorBinaryForward (R := A) (S := B) α M N).val.app W
      ((changeOfRingsHomOfUniverses.{vC, uC, u, u} α _ (tensorPresentation A M N).hom).val.app W
        (scalarExtensionSection (R := A) (S := B) α _ W s (ringedComparisonPure A M N W m n)))) = _
  rw [scalarExtension_map_tmul.{uC, vC, u, u} α, tensorPresentation_pure A,
    scalarTensorBinaryForward_tmul.{uC, vC, u} α, tensorPresentation_inv_pure B]
  rfl

private theorem scalarComparison_inv_pure (M N : SheafOfModules.{u} (base A))
    (W : Eᵒᵖ) (s t : B.obj.obj W) (m : M.val.obj W) (n : N.val.obj W) :
    (scalarComparison α M N).inv.val.app W
      (ringedComparisonPure B _ _ W
        (ringedComparisonScalarSection α M W s m)
        (ringedComparisonScalarSection α N W t n)) =
    ringedComparisonScalarSection α _ W (s * t) (ringedComparisonPure A M N W m n) := by
  change (changeOfRingsHomOfUniverses.{vC, uC, u, u} α _ (tensorPresentation A M N).inv).val.app W
    ((scalarTensorBinaryInverse (R := A) (S := B) α M N).val.app W
      ((tensorPresentation B _ _).hom.val.app W
        (ringedComparisonPure B _ _ W
          (ringedComparisonScalarSection α M W s m)
          (ringedComparisonScalarSection α N W t n)))) = _
  rw [tensorPresentation_pure B]
  change (changeOfRingsHomOfUniverses.{vC, uC, u, u} α _ (tensorPresentation A M N).inv).val.app W
    ((scalarTensorBinaryInverse (R := A) (S := B) α M N).val.app W
      (siteSheafTensorTmul (A := B) _ _ W (scalarExtensionSection (R := A) (S := B) α M W s m)
        (scalarExtensionSection (R := A) (S := B) α N W t n))) = _
  rw [scalarTensorBinaryInverse_tmul.{uC, vC, u} α,
    scalarExtension_map_tmul.{uC, vC, u, u} α, tensorPresentation_inv_pure A]
  rfl
attribute [local irreducible] scalarComparison tensorPresentation

/-- Compose the inverse-image and scalar tensor identifications.
Source: Stacks 03EL and Section 03EK. -/
private noncomputable def scalarComposite
    {X M N : SheafOfModules.{u} (base A)}
    {LX LM LN : SheafOfModules.{u} (base B)}
    (a : X ≅ (monoidalCategory A).tensorObj M N)
    (ex : LX ≅ changeOfRings α X) (em : LM ≅ changeOfRings α M)
    (en : LN ≅ changeOfRings α N) : LX ≅ (monoidalCategory B).tensorObj LM LN :=
  ex ≪≫ (extension α).mapIso a ≪≫ scalarComparison α M N ≪≫ (em.symm ⊗ᵢ en.symm)

private theorem scalarComposite_pure
    {X M N : SheafOfModules.{u} (base A)}
    {LX LM LN : SheafOfModules.{u} (base B)}
    (a : X ≅ (monoidalCategory A).tensorObj M N)
    (ex : LX ≅ changeOfRings α X) (em : LM ≅ changeOfRings α M)
    (en : LN ≅ changeOfRings α N) (W : Eᵒᵖ) (s : B.obj.obj W)
    (m : M.val.obj W) (n : N.val.obj W) :
    (scalarComposite α a ex em en).hom.val.app W
      (ex.inv.val.app W (ringedComparisonScalarSection α X W s
        (a.inv.val.app W (ringedComparisonPure A M N W m n)))) =
    ringedComparisonPure B LM LN W
      (em.inv.val.app W (ringedComparisonScalarSection α M W s m))
      (en.inv.val.app W (ringedComparisonScalarSection α N W 1 n)) := by
  simp only [scalarComposite, Iso.trans_hom, Functor.mapIso_hom,
    tensorIso_hom, Iso.symm_hom, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  have hx (x : (changeOfRings α X).val.obj W) : ex.hom.val.app W
      (ex.inv.val.app W x) = x := congrArg (fun f ↦ f.val.app W x) ex.inv_hom_id
  rw [hx]
  change (em.inv ⊗ₘ en.inv).val.app W ((scalarComparison α M N).hom.val.app W
    ((changeOfRingsHom α X a.hom).val.app W
      (ringedComparisonScalarSection α X W s
        (a.inv.val.app W (ringedComparisonPure A M N W m n))))) = _
  rw [scalarMap_tmul α]
  have hc := congrArg (fun f ↦ f.val.app W (ringedComparisonPure A M N W m n))
    a.inv_hom_id
  change a.hom.val.app W (a.inv.val.app W (ringedComparisonPure A M N W m n)) =
    ringedComparisonPure A M N W m n at hc
  rw [hc, scalarComparison_pure α]
  exact CochainScalarConstruction.pure_map B em.inv en.inv W _ _

private theorem scalarComposite_inv_pure
    {X M N : SheafOfModules.{u} (base A)}
    {LX LM LN : SheafOfModules.{u} (base B)}
    (a : X ≅ (monoidalCategory A).tensorObj M N)
    (ex : LX ≅ changeOfRings α X) (em : LM ≅ changeOfRings α M)
    (en : LN ≅ changeOfRings α N) (W : Eᵒᵖ) (s t : B.obj.obj W)
    (m : M.val.obj W) (n : N.val.obj W) :
    (scalarComposite α a ex em en).inv.val.app W
      (ringedComparisonPure B LM LN W
        (em.inv.val.app W (ringedComparisonScalarSection α M W s m))
        (en.inv.val.app W (ringedComparisonScalarSection α N W t n))) =
    ex.inv.val.app W (ringedComparisonScalarSection α X W (s * t)
      (a.inv.val.app W (ringedComparisonPure A M N W m n))) := by
  simp only [scalarComposite, Iso.trans_inv, Functor.mapIso_inv,
    tensorIso_inv, Iso.symm_inv, comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change ex.inv.val.app W ((changeOfRingsHom α _ a.inv).val.app W
    ((scalarComparison α M N).inv.val.app W
      ((em.hom ⊗ₘ en.hom).val.app W (ringedComparisonPure B LM LN W _ _)))) = _
  erw [CochainScalarConstruction.pure_map B]
  have hm (x : (changeOfRings α M).val.obj W) : em.hom.val.app W
      (em.inv.val.app W x) = x := congrArg (fun f ↦ f.val.app W x) em.inv_hom_id
  have hn (x : (changeOfRings α N).val.obj W) : en.hom.val.app W
      (en.inv.val.app W x) = x := congrArg (fun f ↦ f.val.app W x) en.inv_hom_id
  rw [hm, hn]
  change ex.inv.val.app W ((changeOfRingsHom α _ a.inv).val.app W
    ((scalarComparison α M N).inv.val.app W
      (ringedComparisonPure B _ _ W
        (ringedComparisonScalarSection α M W s m)
        (ringedComparisonScalarSection α N W t n)))) = _
  rw [scalarComparison_inv_pure α, scalarMap_tmul α]

attribute [local irreducible] scalarComposite

end Scalar

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{u}) (RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI)


set_option maxHeartbeats 600000 in
-- Recover the rank-one module comparison from the transported scalar action.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverseImage_unit_iso :
    ∃ e : I.modules.obj
        (unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≅
        unit ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj RI),
      (sets RI).map e.hom = I.moduleUnderlying.hom.app
        (unit ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ≫
          I.ringUnderlying.hom := by
  exact SheafOfModules.inverseImage_unit_iso uInv I



end RingedMate

attribute [local irreducible] RingedMate.scalarComposite RingedMate.scalarComparison
  RingedMate.tensorPresentation

section
attribute [local irreducible] monoidalCategory

private theorem comparison_unit_equation
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uAdj : uInv ⊣ v.sheafPushforwardContinuous (Type u) JC JD)
    [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (α : RI ⟶ S)
    (φ : ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{u} JC JD).obj ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S))
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
      L.obj M = changeOfRings.{vD, uD, u} α (I.modules.obj M))
    (am : L ⊣ (pushforward.{u} φ))
    (hunit : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (U : Cᵒᵖ) (m : M.val.obj U),
      (am.unit.app M).val.app U m =
        (eqToHom (hobj M).symm).val.app (v.op.obj U)
          (ringedComparisonScalarSection α (I.modules.obj M) (v.op.obj U) 1
            ((I.moduleUnderlying.inv.app M).hom.app (v.op.obj U)
              ((uAdj.unit.app ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj
      M)).hom.app U m))))
    [(pushforward.{u} φ).LaxMonoidal]
    (hlax : ∀ (H K : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) (U : Cᵒᵖ)
      (m : ((pushforward.{u} φ).obj H).val.obj U) (n : ((pushforward.{u} φ).obj K).val.obj U),
      (Functor.LaxMonoidal.μ (pushforward.{u} φ) H K).val.app U
        (ringedComparisonPure R _ _ U m n) =
          ringedComparisonPure S H K (v.op.obj U) m n)
    (q : RingedComparisonInsertion R S RI uInv I L)
    (mu : RingedComparisonTensor R S L)
    (hq : ringedComparisonInsertionCondition R S RI uInv I α L hobj q)
    (hpure : ringedComparisonPureCondition R S RI uInv I L q mu)
    (M N : SheafOfModules.{u} (RingedMate.base R)) :
    am.unit.app ((monoidalCategory R).tensorObj M N) ≫
      (pushforward φ).map (mu M N).hom =
      (monoidalCategory R).tensorHom (am.unit.app M) (am.unit.app N) ≫
        Functor.LaxMonoidal.μ (pushforward φ) (L.obj M) (L.obj N) := by
  apply CochainScalarConstruction.pure_hom_ext R
  intro U m n
  let Z := (RingedMate.sets R).obj M ⊗ (RingedMate.sets R).obj N
  let x : Z ⟶ (RingedMate.sets R).obj M := CartesianMonoidalCategory.fst _ _
  let y : Z ⟶ (RingedMate.sets R).obj N := CartesianMonoidalCategory.snd _ _
  let z : Z ⟶ (RingedMate.sets R).obj ((monoidalCategory R).tensorObj M N) :=
    ⟨{ app := fun W ↦ ↾(fun p ↦ ringedComparisonPure R M N W p.1 p.2)
       naturality := by
         intro W V i
         ext p
         exact (CochainScalarConstruction.pure_restrict R M N i p.1 p.2).symm }⟩
  let t := (uAdj.unit.app Z).hom.app U (m, n)
  have hx := congrArg (fun f ↦ f.hom.app U (m, n)) (uAdj.unit.naturality x)
  have hy := congrArg (fun f ↦ f.hom.app U (m, n)) (uAdj.unit.naturality y)
  have hz := congrArg (fun f ↦ f.hom.app U (m, n)) (uAdj.unit.naturality z)
  change (uAdj.unit.app ((RingedMate.sets R).obj M)).hom.app U m =
    (uInv.map x).hom.app (v.op.obj U) t at hx
  change (uAdj.unit.app ((RingedMate.sets R).obj N)).hom.app U n =
    (uInv.map y).hom.app (v.op.obj U) t at hy
  change (uAdj.unit.app ((RingedMate.sets R).obj
    ((monoidalCategory R).tensorObj M N))).hom.app U
      (ringedComparisonPure R M N U m n) =
    (uInv.map z).hom.app (v.op.obj U) t at hz
  have hp := hpure M N Z x y z (fun _ _ ↦ rfl) (v.op.obj U) t
  change (mu M N).hom.val.app (v.op.obj U)
    ((q _).hom.app (v.op.obj U)
      ((I.moduleUnderlying.inv.app _).hom.app (v.op.obj U)
        ((uInv.map z).hom.app (v.op.obj U) t))) =
    ringedComparisonPure S _ _ (v.op.obj U)
      ((q M).hom.app (v.op.obj U)
        ((I.moduleUnderlying.inv.app M).hom.app (v.op.obj U)
          ((uInv.map x).hom.app (v.op.obj U) t)))
      ((q N).hom.app (v.op.obj U)
        ((I.moduleUnderlying.inv.app N).hom.app (v.op.obj U)
          ((uInv.map y).hom.app (v.op.obj U) t))) at hp
  have hη (Q : SheafOfModules.{u} (RingedMate.base R)) (r : Q.val.obj U) :
      (q Q).hom.app (v.op.obj U)
        ((I.moduleUnderlying.inv.app Q).hom.app (v.op.obj U)
          ((uAdj.unit.app ((RingedMate.sets R).obj Q)).hom.app U r)) =
      (am.unit.app Q).val.app U r := (hq Q (v.op.obj U) _).trans (hunit Q U r).symm
  rw [← hx, ← hy, ← hz, hη, hη, hη] at hp
  change (mu M N).hom.val.app (v.op.obj U)
    ((am.unit.app _).val.app U (ringedComparisonPure R M N U m n)) =
    (Functor.LaxMonoidal.μ (pushforward φ) (L.obj M) (L.obj N)).val.app U
      (((monoidalCategory R).tensorHom (am.unit.app M) (am.unit.app N)).val.app U
        (ringedComparisonPure R M N U m n))
  have hm := CochainScalarConstruction.pure_map R (am.unit.app M) (am.unit.app N) U m n
  change ((monoidalCategory R).tensorHom (am.unit.app M) (am.unit.app N)).val.app U
    (ringedComparisonPure R M N U m n) = ringedComparisonPure R _ _ U
      ((am.unit.app M).val.app U m) ((am.unit.app N).val.app U n) at hm
  exact hp.trans ((congrArg (fun r ↦
    (Functor.LaxMonoidal.μ (pushforward φ) (L.obj M) (L.obj N)).val.app U r) hm).trans
      (hlax (L.obj M) (L.obj N) U _ _)).symm

end

attribute [local irreducible] scalarExtensionUnitIso

set_option maxHeartbeats 1000000 in
-- Assemble both tensor factors and identify the tensor and unit mates.
/-- The actual oplax mate equals every normalized ringed tensor comparison, and its
scalar and unit maps have the stated inverse formulas.
Source: Stacks Project, Modules on Sites, Tags 03D7 and 03EL;
the identification of the specified mates is the agent expansion of these tags.
(blueprint: lem-pd-ringed-tensor-adjunction-mate).

Proof:
1. Compose the normalized inverse-image tensor isomorphism of
   lem-weil-pbc-algebraic-inverse-image-tensor-comparison with the normalized
   scalar-extension tensor isomorphism of
   lem-weil-pbc-scalar-extension-tensor-comparison. Naturality of scalar insertion
   gives the generalized pure equation of the canonical comparison.
2. Under the specified adjunction, the adjunct of f is unit followed by P(f).
   By lem-sfb-adjunction-oplax-mate, the adjunct of its tensor map is the tensor
   of the two units followed by the stipulated lax pairing.
3. Test the canonical comparison on the product of the two underlying source
   sheaves. Naturality of the geometric unit identifies its adjunct on every
   local pure tensor with this lax pairing. The sheaf tensor bilinear universal
   property makes the adjuncts equal, without asserting that all sheaf tensor
   sections are pure. Injectivity of the adjunction identifies the actual mates.
4. Scalar linearity gives s tensor (m tensor n) mapped to
   (s tensor m) tensor (1 tensor n). The reverse formula multiplies the scalars.
   It is balanced in both RI variables and over S, and commutes with restrictions.
   Extend through both sheafifications using the bilinear-extension universal
   property. The two composites are identities on generators and hence on sheaves.
5. Transport I(R) to RI by the algebraic inverse-image identifications. Scalar
   multiplication s tensor r mapped to s alpha(r) has adjunct c, so it is the
   actual unit mate. Its inverse sends s to s tensor 1; the two inverse equations
   follow by balancing and sheafification uniqueness, also for the zero ring. -/
theorem ringedTensor_adjunction_mate
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
    (JC : GrothendieckTopology C) (JD : GrothendieckTopology D)
    (v : C ⥤ D) [v.IsContinuous JC JD]
    (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
    (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
    (uAdj : uInv ⊣ v.sheafPushforwardContinuous (Type u) JC JD)
    [PreservesFiniteLimits uInv]
    (I : AlgebraicInverseImage uInv R RI) (α : RI ⟶ S)
    (φ : ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⟶
      (v.sheafPushforwardContinuous RingCat.{u} JC JD).obj ((sheafCompose JD (forget₂
      CommRingCat.{u} RingCat.{u})).obj S))
    (hφ : (sheafCompose JC (CategoryTheory.forget RingCat.{u})).map φ =
      uAdj.homEquiv _ _ (I.ringUnderlying.hom ≫
        (sheafCompose JD (CategoryTheory.forget CommRingCat.{u})).map α))
    (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
    (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
      L.obj M = changeOfRings.{vD, uD, u} α (I.modules.obj M))
    (hmap : ∀ {M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ N),
      L.map f = eqToHom (hobj M) ≫
        changeOfRingsHom.{vD, uD, u} α (I.modules.obj M) (I.modules.map f) ≫
          eqToHom (hobj N).symm)
    (am : L ⊣ (pushforward.{u} φ))
    (hunit : ∀ (M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) (U : Cᵒᵖ) (m : M.val.obj U),
      (am.unit.app M).val.app U m =
        (eqToHom (hobj M).symm).val.app (v.op.obj U)
          (ringedComparisonScalarSection α (I.modules.obj M) (v.op.obj U) 1
            ((I.moduleUnderlying.inv.app M).hom.app (v.op.obj U)
              ((uAdj.unit.app ((toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R) ⋙ sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj
      M)).hom.app U m))))
    [(pushforward.{u} φ).LaxMonoidal]
    (hlax : ∀ (H K : SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)) (U : Cᵒᵖ)
      (m : ((pushforward.{u} φ).obj H).val.obj U) (n : ((pushforward.{u} φ).obj K).val.obj U),
      (Functor.LaxMonoidal.μ (pushforward.{u} φ) H K).val.app U
        (ringedComparisonPure R _ _ U m n) =
          ringedComparisonPure S H K (v.op.obj U) m n)
    (hlaxUnit : ∀ (U : Cᵒᵖ) (r : R.obj.obj U),
      (Functor.LaxMonoidal.ε (pushforward.{u} φ)).val.app U r = φ.hom.app U r) :
    ∃ (k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I α L hobj)
      (a : ∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R),
        I.modules.obj ((monoidalCategory R).tensorObj M N) ≅
          (monoidalCategory RI).tensorObj (I.modules.obj M) (I.modules.obj N))
      (j : I.modules.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ≅ (SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj RI)))
      (e₀ : L.obj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)) ≅ SheafOfModules.unit ((sheafCompose JD (forget₂ CommRingCat.{u}
      RingCat.{u})).obj S)),
      (∀ {M M' N N' : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R)} (f : M ⟶ M') (g : N ⟶ N'),
        I.modules.map ((monoidalCategory R).tensorHom f g) ≫ (a M' N').hom =
          (a M N).hom ≫ (monoidalCategory RI).tensorHom
            (I.modules.map f) (I.modules.map g)) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (Z : Sheaf JC (Type u))
        (x : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj M) (y : Z ⟶ (toSheaf
      ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙ sheafCompose JC
      (CategoryTheory.forget AddCommGrpCat.{u})).obj N)
        (z : Z ⟶ (toSheaf ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⋙
      sheafCompose JC (CategoryTheory.forget AddCommGrpCat.{u})).obj ((monoidalCategory
      R).tensorObj M N)),
        (∀ (U : Cᵒᵖ) (t : Z.obj.obj U), z.hom.app U t =
          ringedComparisonPure R M N U (x.hom.app U t) (y.hom.app U t)) →
        ∀ (W : Dᵒᵖ) (t : (uInv.obj Z).obj.obj W),
          (a M N).hom.val.app W
            ((uInv.map z ≫ I.moduleUnderlying.inv.app
              ((monoidalCategory R).tensorObj M N)).hom.app W t) =
          ringedComparisonPure RI (I.modules.obj M) (I.modules.obj N) W
            ((uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t)
            ((uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t)) ∧
      (∀ (W : Dᵒᵖ) (r : (I.modules.obj (SheafOfModules.unit ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))).val.obj W),
        j.hom.val.app W r = I.ringUnderlying.hom.hom.app W
          ((I.moduleUnderlying.hom.app (SheafOfModules.unit ((sheafCompose JC (forget₂
      CommRingCat.{u} RingCat.{u})).obj R))).hom.app W r)) ∧
      (∀ (k' : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I α L hobj)
        (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R)),
        am.leftAdjointOplaxMonoidal.δ M N = (k'.mu M N).hom) ∧
      (∀ M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      IsIso (am.leftAdjointOplaxMonoidal.δ M N)) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (W : Dᵒᵖ) (s : S.obj.obj W)
        (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W),
        (am.leftAdjointOplaxMonoidal.δ M N).val.app W
          ((eqToHom (hobj ((monoidalCategory R).tensorObj M N)).symm).val.app W
            (ringedComparisonScalarSection α _ W s
              ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n)))) =
        ringedComparisonPure S _ _ W
          ((eqToHom (hobj M).symm).val.app W
            (ringedComparisonScalarSection α _ W s m))
          ((eqToHom (hobj N).symm).val.app W
            (ringedComparisonScalarSection α _ W 1 n))) ∧
      (∀ (M N : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj
      R)) (W : Dᵒᵖ) (s t : S.obj.obj W)
        (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W),
        (k.mu M N).inv.val.app W
          (ringedComparisonPure S _ _ W
            ((eqToHom (hobj M).symm).val.app W
              (ringedComparisonScalarSection α _ W s m))
            ((eqToHom (hobj N).symm).val.app W
              (ringedComparisonScalarSection α _ W t n))) =
        (eqToHom (hobj ((monoidalCategory R).tensorObj M N)).symm).val.app W
          (ringedComparisonScalarSection α _ W (s * t)
            ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n)))) ∧
      e₀.hom = am.leftAdjointOplaxMonoidal.η ∧
      (∀ (W : Dᵒᵖ) (s : S.obj.obj W) (r : RI.obj.obj W),
        e₀.hom.val.app W
          ((eqToHom (hobj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))).symm).val.app W
            (ringedComparisonScalarSection α _ W s (j.inv.val.app W r))) =
        s * α.hom.app W r) ∧
      (∀ (W : Dᵒᵖ) (s : S.obj.obj W),
        e₀.inv.val.app W s =
          (eqToHom (hobj (SheafOfModules.unit ((sheafCompose JC (forget₂ CommRingCat.{u}
      RingCat.{u})).obj R))).symm).val.app W
            (ringedComparisonScalarSection α _ W s
              (j.inv.val.app W
                ((1 : RI.obj.obj W) :
                  (SheafOfModules.unit
                    ((sheafCompose JD
                      (forget₂ CommRingCat.{u} RingCat.{u})).obj RI)).val.obj W)))) := by
  classical
  let := monoidalCategory.{vC, uC, u} R
  let := monoidalCategory.{vD, uD, u} RI
  let := monoidalCategory.{vD, uD, u} S
  obtain ⟨a, ha, hp⟩ := CochainInversePairing.exists_inverseImageTensorComparison R RI uInv I
    (v.sheafPushforwardContinuous (Type u) JC JD) uAdj
  let T := RingedMate.extension α
  let ε : L ≅ I.modules ⋙ T := NatIso.ofComponents
    (fun M ↦ eqToIso (hobj M)) (by
      intro M N f
      change L.map f ≫ eqToHom (hobj N) =
        eqToHom (hobj M) ≫ changeOfRingsHom α (I.modules.obj M) (I.modules.map f)
      rw [hmap]
      simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id])
  let q : RingedComparisonInsertion R S RI uInv I L := fun M ↦
    ⟨{ app := fun W ↦ ↾fun m ↦ (ε.inv.app M).val.app W
          (ringedComparisonScalarSection α (I.modules.obj M) W 1 m)
       naturality := by
         intro W V i
         ext m
         change (ε.inv.app M).val.app V
           (ringedComparisonScalarSection α (I.modules.obj M) V 1 ((I.modules.obj M).val.map i m)) =
           (L.obj M).val.map i ((ε.inv.app M).val.app W
             (ringedComparisonScalarSection α (I.modules.obj M) W 1 m))
         have h := scalarExtensionSection_naturality α (I.modules.obj M) i 1 m
         rw [map_one] at h
         change (changeOfRings α (I.modules.obj M)).val.map i
           (ringedComparisonScalarSection α (I.modules.obj M) W 1 m) =
             ringedComparisonScalarSection α (I.modules.obj M) V 1
               ((I.modules.obj M).val.map i m) at h
         rw [← h]
         exact PresheafOfModules.naturality_apply (ε.inv.app M).val i _ }⟩
  have hq : ringedComparisonInsertionCondition R S RI uInv I α L hobj q :=
    fun _ _ _ ↦ rfl
  let mu : RingedComparisonTensor R S L := fun M N ↦
    RingedMate.scalarComposite α (a M N) (ε.app (M ⊗ N)) (ε.app M) (ε.app N)
  have hε (M : SheafOfModules.{u} (RingedMate.base R))
      (W : Dᵒᵖ) (x : (T.obj (I.modules.obj M)).val.obj W) :
      (ε.hom.app M).val.app W ((ε.inv.app M).val.app W x) = x :=
    congrArg (fun f ↦ f.val.app W x) (ε.inv_hom_id_app M)
  have hforward (M N : SheafOfModules.{u} (RingedMate.base R))
      (W : Dᵒᵖ) (s : S.obj.obj W)
      (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W) :
      (mu M N).hom.val.app W
        ((ε.inv.app (M ⊗ N)).val.app W
          (ringedComparisonScalarSection α _ W s
            ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n)))) =
      ringedComparisonPure S _ _ W
        ((ε.inv.app M).val.app W (ringedComparisonScalarSection α _ W s m))
        ((ε.inv.app N).val.app W (ringedComparisonScalarSection α _ W 1 n)) := by
    exact RingedMate.scalarComposite_pure α (a M N)
      (ε.app (M ⊗ N)) (ε.app M) (ε.app N) W s m n
  have hbackward (M N : SheafOfModules.{u} (RingedMate.base R))
      (W : Dᵒᵖ) (s t : S.obj.obj W)
      (m : (I.modules.obj M).val.obj W) (n : (I.modules.obj N).val.obj W) :
      (mu M N).inv.val.app W
        (ringedComparisonPure S _ _ W
          ((ε.inv.app M).val.app W (ringedComparisonScalarSection α _ W s m))
          ((ε.inv.app N).val.app W (ringedComparisonScalarSection α _ W t n))) =
      (ε.inv.app (M ⊗ N)).val.app W
        (ringedComparisonScalarSection α _ W (s * t)
          ((a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n))) := by
    exact RingedMate.scalarComposite_inv_pure α (a M N)
      (ε.app (M ⊗ N)) (ε.app M) (ε.app N) W s t m n
  have hnormal : ringedComparisonPureCondition R S RI uInv I L q mu := by
    intro M N Z x y z hz W t
    let d := (uInv.map z ≫ I.moduleUnderlying.inv.app (M ⊗ N)).hom.app W t
    let m := (uInv.map x ≫ I.moduleUnderlying.inv.app M).hom.app W t
    let n := (uInv.map y ≫ I.moduleUnderlying.inv.app N).hom.app W t
    have hd : d = (a M N).inv.val.app W (ringedComparisonPure RI _ _ W m n) := by
      have h := congrArg ((a M N).inv.val.app W) (hp M N Z x y z hz W t)
      have hc := congrArg (fun f ↦ f.val.app W d) (a M N).hom_inv_id
      exact hc.symm.trans h
    change (mu M N).hom.val.app W
      ((ε.inv.app (M ⊗ N)).val.app W (ringedComparisonScalarSection α _ W 1 d)) = _
    rw [hd]
    exact hforward M N W 1 m n
  have heq (q' : RingedComparisonInsertion R S RI uInv I L)
      (mu' : RingedComparisonTensor R S L)
      (hq' : ringedComparisonInsertionCondition R S RI uInv I α L hobj q')
      (hp' : ringedComparisonPureCondition R S RI uInv I L q' mu')
      (M N : SheafOfModules.{u} (RingedMate.base R)) :
      am.leftAdjointOplaxMonoidal.δ M N = (mu' M N).hom := by
    exact tensorMate_eq am M N _
      (comparison_unit_equation JC JD v R S RI uInv uAdj I α φ L hobj am
        hunit hlax q' mu' hq' hp' M N)
  have hmate := heq q mu hq hnormal
  let k : CanonicalRingedTensorComparisonOnSmallSites R S RI uInv I α L hobj :=
    { q := q
      q_one := hq
      mu := mu
      pure := hnormal
      naturality := fun f g ↦ tensorMate_natural am mu hmate f g }
  obtain ⟨j, hj⟩ := RingedMate.inverseImage_unit_iso R RI uInv I
  let U := unit (RingedMate.base R)
  let e₀ : L.obj U ≅ unit (RingedMate.base S) :=
    ε.app U ≪≫ T.mapIso j ≪≫ scalarExtensionUnitIso α
  have hjsection (W : Dᵒᵖ) (r : (I.modules.obj U).val.obj W) :
      j.hom.val.app W r = I.ringUnderlying.hom.hom.app W
        ((I.moduleUnderlying.hom.app U).hom.app W r) :=
    congrArg (fun f ↦ f.hom.app W r) hj
  have hunitforward (W : Dᵒᵖ) (s : S.obj.obj W) (r : RI.obj.obj W) :
      e₀.hom.val.app W ((ε.inv.app U).val.app W
        (ringedComparisonScalarSection α _ W s (j.inv.val.app W r))) = s * α.hom.app W r := by
    simp only [e₀, Iso.trans_hom, Functor.mapIso_hom,
      comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    change (scalarExtensionUnitIso α).hom.val.app W
      ((changeOfRingsHom.{vD, uD, u} α _ j.hom).val.app W
        ((ε.hom.app U).val.app W ((ε.inv.app U).val.app W
          (ringedComparisonScalarSection α _ W s (j.inv.val.app W r))))) = _
    rw [hε, RingedMate.scalarMap_tmul α]
    have hc := congrArg (fun f ↦ f.val.app W r) j.inv_hom_id
    change j.hom.val.app W (j.inv.val.app W r) = r at hc
    rw [hc]
    exact scalarExtensionUnitIso_tmul.{uD, vD, u} α W s r
  have hunitmate : e₀.hom = am.leftAdjointOplaxMonoidal.η := by
    apply unitMate_eq am
    apply hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change R.obj.obj W at r
    change e₀.hom.val.app (v.op.obj W) ((am.unit.app U).val.app W r) =
      (Functor.LaxMonoidal.ε (pushforward φ)).val.app W r
    erw [hunit, hlaxUnit]
    let d := (I.moduleUnderlying.inv.app U).hom.app (v.op.obj W)
      ((uAdj.unit.app ((RingedMate.sets R).obj U)).hom.app W r)
    have hd : d = j.inv.val.app (v.op.obj W) (j.hom.val.app (v.op.obj W) d) :=
      (congrArg (fun f ↦ f.val.app (v.op.obj W) d) j.hom_inv_id).symm
    change e₀.hom.val.app (v.op.obj W) ((ε.inv.app U).val.app (v.op.obj W)
      (ringedComparisonScalarSection α _ (v.op.obj W) 1 d)) = φ.hom.app W r
    rw [hd, hunitforward, one_mul]
    have hc := congrArg (fun f ↦ f.hom.app (v.op.obj W)
      ((uAdj.unit.app ((RingedMate.sets R).obj U)).hom.app W r))
        (I.moduleUnderlying.inv_hom_id_app U)
    rw [hjsection]
    change (I.moduleUnderlying.hom.app U).hom.app (v.op.obj W) d = _ at hc
    rw [hc]
    have h := congrArg (fun f ↦ f.hom.app W r) hφ
    rw [Adjunction.homEquiv_unit] at h
    exact h.symm
  refine ⟨k, a, j, e₀, ha, hp, hjsection, ?_, ?_, ?_, ?_, hunitmate, hunitforward, ?_⟩
  · intro k' M N
    exact heq k'.q k'.mu k'.q_one k'.pure M N
  · intro M N
    rw [hmate]
    infer_instance
  · intro M N W s m n
    rw [hmate]
    exact hforward M N W s m n
  · exact hbackward
  · intro W s
    let x := (ε.inv.app U).val.app W (ringedComparisonScalarSection α _ W s
      (j.inv.val.app W (1 : RI.obj.obj W)))
    have h : e₀.hom.val.app W x = s := by
      change e₀.hom.val.app W ((ε.inv.app U).val.app W
        (ringedComparisonScalarSection α _ W s
          (j.inv.val.app W (1 : RI.obj.obj W)))) = s
      rw [hunitforward, map_one, mul_one]
    have hi := congrArg (e₀.inv.val.app W) h
    exact hi.symm.trans (congrArg (fun f ↦ f.val.app W x) e₀.hom_inv_id)

end SheafOfModules
