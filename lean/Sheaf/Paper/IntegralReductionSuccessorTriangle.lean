/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X3
-/
module

public import Sheaf.Paper.IntegralReductionTower
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.IntegralPrincipalReductionCoefficients
import all Sheaf.Paper.IntegralReductionTowerUnrestricted
import Sheaf.Paper.DerivedReductionResolutionIndependence
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Endomorphism
import all Sheaf.Paper.AdicReductionTriangle
import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients

/-! # Successive derived DVR reductions

The coefficient exponent at tower index n is n+1.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open SheafOfModules SheafOfModules.PrincipalReduction
namespace IntegralSuccessorProof
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{r}] [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
variable (O S : Sheaf J CommRingCat.{r}) (U : C) (hU : IsTerminal U)
  (t : O.obj.obj (op U)) (φ : O ⟶ S)
private abbrev Omod (O : Sheaf J CommRingCat.{r}) : Sheaf J RingCat.{r} :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj O
private abbrev restriction {O S : Sheaf J CommRingCat.{r}} (φ : O ⟶ S) :=
  (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).map φ
private noncomputable def coefficientMultiplication : End (unit.{v, u, r} (Omod O)) where
  val :=
    { app := fun V ↦ by
        change ModuleCat.of (O.obj.obj V) (O.obj.obj V) ⟶
          ModuleCat.of (O.obj.obj V) (O.obj.obj V)
        exact ModuleCat.ofHom
          { toFun := fun x ↦ O.obj.map (hU.from V.unop).op t * x
            map_add' := mul_add _
            map_smul' := fun b x ↦ mul_left_comm _ _ _ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change O.obj.obj V at x
        symm
        change O.obj.map f (_ * x) = _ * O.obj.map f x
        rw [map_mul]
        congr 1
        rw [← ConcreteCategory.comp_apply, ← O.obj.map_comp]
        have hh : (hU.from V.unop).op ≫ f =
            (hU.from W.unop).op := by
          apply Quiver.Hom.unop_inj
          exact hU.hom_ext _ _
        rw [hh] }

private noncomputable def coefficientProjection :
    unit.{v, u, r} (Omod O) ⟶ (restrictScalars.{r, v, r, u} (restriction φ)).obj (unit.{v, u, r}
      (Omod S)) where
  val :=
    { app := fun V ↦ by
        change ModuleCat.of (O.obj.obj V) (O.obj.obj V) ⟶
          (ModuleCat.restrictScalars (φ.hom.app V).hom).obj
            (ModuleCat.of (S.obj.obj V) (S.obj.obj V))
        exact ModuleCat.ofHom
          (Y := (ModuleCat.restrictScalars (φ.hom.app V).hom).obj
            (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
          { toFun := φ.hom.app V
            map_add' := map_add _
            map_smul' := fun b x ↦ by
              change φ.hom.app V (b * x) = φ.hom.app V b * φ.hom.app V x
              exact map_mul _ _ _ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (φ.hom.naturality f) x }

private theorem coefficientMultiplication_underlying :
    (toSheaf.{r, v, u, r} (Omod O)).map (coefficientMultiplication (O := O) (U := U) (hU := hU) (t
      := t)) =
      sectionMultiplication.{u, v, r} O U hU t := by
  apply (existsUnique_sectionMultiplication.{u, v, r} O U hU t).unique
  · intro V x
    rfl
  · exact (existsUnique_sectionMultiplication.{u, v, r} O U hU t).exists.choose_spec

private theorem coefficient_zero
    (hz : sectionMultiplication.{u, v, r} O U hU t ≫
      (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r}
        AddCommGrpCat.{r})).map φ = 0) :
    (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t)) ≫ (coefficientProjection (O :=
      O) (S := S) (φ := φ)) = 0 := by
  apply (toSheaf.{r, v, u, r} (Omod O)).map_injective
  rw [Functor.map_comp, coefficientMultiplication_underlying]
  ext V x
  exact congrArg (fun f ↦ f.hom.app V x) hz

private theorem coefficient_shortExact
    (hz : sectionMultiplication.{u, v, r} O U hU t ≫
      (sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r}
        AddCommGrpCat.{r})).map φ = 0)
    (hs : (ShortComplex.mk (sectionMultiplication.{u, v, r} O U hU t)
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r} ⋙ forget₂ RingCat.{r}
        AddCommGrpCat.{r})).map φ)
        hz).ShortExact) :
    (ShortComplex.mk (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t))
      (coefficientProjection (O := O) (S := S) (φ := φ))
      (coefficient_zero (O := O) (S := S) (U := U) (hU := hU) (t := t) (φ := φ) hz)).ShortExact :=
        by
  apply ShortExact.reflects_shortExact_of_faithful (toSheaf.{r, v, u, r} (Omod O))
  have e : (ShortComplex.mk (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t))
    (coefficientProjection (O := O) (S := S) (φ := φ))
      (coefficient_zero (O := O) (S := S) (U := U) (hU := hU) (t := t) (φ := φ) hz)).map
        (toSheaf.{r, v, u, r} (Omod O)) ≅
      ShortComplex.mk (sectionMultiplication.{u, v, r} O U hU t)
        ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r} ⋙
          forget₂ RingCat.{r} AddCommGrpCat.{r})).map φ) hz :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by
        change 𝟙 _ ≫ sectionMultiplication.{u, v, r} O U hU t =
          (toSheaf.{r, v, u, r} (Omod O)).map (coefficientMultiplication (O := O) (U := U) (hU :=
            hU) (t := t)) ≫ 𝟙 _
        simp only [Category.id_comp, Category.comp_id]
        exact (coefficientMultiplication_underlying (O := O) (U := U) (hU := hU) (t := t)).symm)
      (by ext V x; rfl)
  exact (ShortComplex.shortExact_iff_of_iso e).2 hs

omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
private theorem coefficientMultiplication_pow (k : ℕ) :
    (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t)) ^ k =
      coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t ^ k) := by
  induction k with
  | zero =>
    change (𝟙 (unit (Omod O))) = _
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.obj V at x
    change x = O.obj.map (hU.from V.unop).op (t ^ 0) * x
    rw [pow_zero, map_one, one_mul]
  | succ k ih =>
    rw [pow_succ, ih]
    change (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t)) ≫
      (coefficientMultiplication (O := O) (U := U) (hU := hU) (t := t ^ k)) = _
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change O.obj.obj V at x
    change O.obj.map (hU.from V.unop).op (t ^ k) *
        (O.obj.map (hU.from V.unop).op t * x) =
      O.obj.map (hU.from V.unop).op (t ^ (k + 1)) * x
    rw [pow_succ, map_mul, mul_assoc]

variable {S' : Sheaf J CommRingCat.{r}} (φ' : O ⟶ S') (ρ : S' ⟶ S)
  (hρ : φ' ≫ ρ = φ)
private noncomputable def coefficientTransition (hρ : φ' ≫ ρ = φ) :
    (restrictScalars.{r} (restriction φ')).obj (unit (Omod S')) ⟶
      (restrictScalars.{r} (restriction φ)).obj (unit (Omod S)) where
  val :=
    { app := fun V ↦ ModuleCat.ofHom
        (X := (ModuleCat.restrictScalars (φ'.hom.app V).hom).obj
          (ModuleCat.of (S'.obj.obj V) (S'.obj.obj V)))
        (Y := (ModuleCat.restrictScalars (φ.hom.app V).hom).obj
          (ModuleCat.of (S.obj.obj V) (S.obj.obj V)))
        { toFun := ρ.hom.app V
          map_add' := map_add _
          map_smul' := fun b x ↦ by
            change S'.obj.obj V at x
            change O.obj.obj V at b
            change ρ.hom.app V (φ'.hom.app V b * x) =
              φ.hom.app V b * ρ.hom.app V x
            rw [map_mul]
            congr 1
            exact congrArg (fun h : O ⟶ S ↦ (h.hom.app V).hom b) hρ }
      naturality := by
        intro V W f
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact ConcreteCategory.congr_hom (ρ.hom.naturality f) x }
omit [HasSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat] in
private theorem coefficientTransition_projection :
    coefficientProjection (O := O) (S := S') (φ := φ') ≫
      coefficientTransition (O := O) (S := S) (φ := φ) (φ' := φ') (ρ := ρ) (hρ := hρ) =
        coefficientProjection (O := O) (S := S) (φ := φ) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun h : O ⟶ S ↦ (h.hom.app V).hom x) hρ

end IntegralSuccessorProof

namespace IntegralSuccessorProof
open CategoryTheory.Category
variable {C : Type u} [Category.{v} C] [Abelian C]
private def quotientPresentationIso {X Y Z : C} (f : X ⟶ Y) (p : Y ⟶ Z)
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact) : cokernel f ≅ Z :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hs.gIsCokernel
private theorem quotientPresentationIso_hom {X Y Z : C} (f : X ⟶ Y) (p : Y ⟶ Z)
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact) :
    cokernel.π f ≫ (quotientPresentationIso f p hz hs).hom = p :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel f)
    hs.gIsCokernel WalkingParallelPair.one
private theorem quotientPresentationIso_inv {X Y Z : C} (f : X ⟶ Y) (p : Y ⟶ Z)
    (hz : f ≫ p = 0) (hs : (ShortComplex.mk f p hz).ShortExact) :
    p ≫ (quotientPresentationIso f p hz hs).inv = cokernel.π f := by
  apply (Iso.comp_inv_eq _).2
  exact (quotientPresentationIso_hom f p hz hs).symm
private theorem successorCoefficientSequence
    {U B₀ B₁ B₂ : C} (f g : U ⟶ U)
    (p₀ : U ⟶ B₀) (p₁ : U ⟶ B₁) (p₂ : U ⟶ B₂)
    (h₀ : f ≫ p₀ = 0) (h₁ : g ≫ p₁ = 0) (h₂ : (f ≫ g) ≫ p₂ = 0)
    (hs₀ : (ShortComplex.mk f p₀ h₀).ShortExact)
    (hs₁ : (ShortComplex.mk g p₁ h₁).ShortExact)
    (hs₂ : (ShortComplex.mk (f ≫ g) p₂ h₂).ShortExact)
    (q : B₂ ⟶ B₁) (hq : p₂ ≫ q = p₁) :
    ∃ i : B₀ ⟶ B₂, ∃ hz : i ≫ q = 0, (ShortComplex.mk i q hz).ShortExact := by
  let e₀ := quotientPresentationIso f p₀ h₀ hs₀
  let e₁ := quotientPresentationIso g p₁ h₁ hs₁
  let e₂ := quotientPresentationIso (f ≫ g) p₂ h₂ hs₂
  let S := kernelCokernelCompSequence.snakeInput f g
  let i := e₀.inv ≫ S.L₃.f ≫ e₂.hom
  have : Mono g := hs₁.mono_f
  have : Epi p₂ := hs₂.epi_g
  have heq : q = e₂.inv ≫ S.L₃.g ≫ e₁.hom := by
    apply (cancel_epi p₂).1
    rw [hq, ← assoc, quotientPresentationIso_inv]
    change p₁ = cokernel.π (f ≫ g) ≫
      cokernel.map (f ≫ g) g f (𝟙 U) (by simp) ≫ e₁.hom
    simp only [cokernel.map, cokernel.π_desc_assoc, id_comp]
    exact (quotientPresentationIso_hom g p₁ h₁ hs₁).symm
  have hz : i ≫ q = 0 := by rw [heq]; simp [i]
  refine ⟨i, hz, ?_⟩
  have hm : Mono S.L₃.f := by
    apply S.L₂'_exact.mono_g
    exact (isZero_kernel_of_mono g).eq_of_src _ _
  have he : Epi S.L₃.g := by
    change Epi (cokernel.map (f ≫ g) g f (𝟙 U) (by simp))
    infer_instance
  have hs : S.L₃.ShortExact := ⟨S.L₃_exact⟩
  apply ShortComplex.shortExact_of_iso _ hs
  exact ShortComplex.isoMk e₀ e₂ e₁ (by simp [i]) (by simp [heq])

end IntegralSuccessorProof


namespace IntegralSuccessorTensorProof
open MonoidalCategory
variable (T : Scheme.{u}) (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1})
local instance : EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{u} _
local instance : HasSheafify (ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u,u} T
local instance : (ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u,u} T
attribute [local instance] isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory
private abbrev Mod := SheafOfModules.{u + 1} ((adicLisseForget T).obj R)
private def tensorLeftSite (B : Mod T R) : Mod T R ⥤ Mod T R where
  obj M := (siteSheafTensorRight (A := R) M).obj B
  map f := siteSheafTensorSecondMap B f
  map_id M := by
    let a := PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)
    change a.map _ = 𝟙 _
    rw [← a.map_id]
    congr 1
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
  map_comp f g := by
    let a := PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)
    change a.map _ = a.map _ ≫ a.map _
    rw [← a.map_comp]
    congr 1
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    rfl
private def coefficientMap {B B' : Mod T R} (f : B ⟶ B') :
    tensorLeftSite T R B ⟶ tensorLeftSite T R B' where
  app M := (siteSheafTensorRight (A := R) M).map f
  naturality _ _ g := (siteSheafTensorSecondMap_naturality f g).symm
private def tensorUnitNatural : 𝟭 (Mod T R) ⟶
    tensorLeftSite T R (unit ((adicLisseForget T).obj R)) where
  app M := (ReductionTensor.tensorUnitIso T R M).inv
  naturality M N f := by
    ext V x
    change (ReductionTensor.tensorUnitIso T R N).inv.val.app V (f.val.app V x) =
      (siteSheafTensorSecondMap (unit ((adicLisseForget T).obj R)) f).val.app V
        ((ReductionTensor.tensorUnitIso T R M).inv.val.app V x)
    rw [ReductionTensor.tensorUnitIso_inv_apply, ReductionTensor.tensorUnitIso_inv_apply]
    have h := (PresheafOfModules.sheafificationAdjunction
      (𝟙 ((adicLisseForget T).obj R).obj)).unit.naturality
        (siteTensorSecondMap (unit ((adicLisseForget T).obj R)).val f.val)
    exact congrArg (fun a ↦ a.app V ((1 : R.obj.obj V) ⊗ₜ[R.obj.obj V] x)) h
private def reductionUnit (B : Mod T R)
    (p : unit ((adicLisseForget T).obj R) ⟶ B) : 𝟭 (Mod T R) ⟶ tensorLeftSite T R B :=
  tensorUnitNatural T R ≫ coefficientMap T R p
private theorem reductionUnit_epi (B : Mod T R)
    (p : unit ((adicLisseForget T).obj R) ⟶ B) [Epi p] (M : Mod T R) :
    Epi ((reductionUnit T R B p).app M) := by
  let := tensorLeft_preservesColimits_independentCoefficients R M
  let : PreservesColimitsOfSize.{0, 0} (tensorLeft M) :=
    preservesColimitsOfSize_shrink (tensorLeft M)
  let : PreservesFiniteColimits (tensorRight M) :=
    preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let : PreservesFiniteColimits (siteSheafTensorRight (A := R) M) :=
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R M).symm
  change Epi ((ReductionTensor.tensorUnitIso T R M).inv ≫
    (siteSheafTensorRight (A := R) M).map p)
  infer_instance
private def reductionIso {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (p : unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (unit ((adicLisseForget T).obj S))) [Epi p]
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V)) :
    tensorLeftSite T R ((pbcRestrict φ).obj (unit ((adicLisseForget T).obj S))) ≅
      pbcExtend φ ⋙ pbcRestrict φ := by
  refine NatIso.ofComponents (ReductionTensor.ordinaryQuotientIso T R φ) ?_
  intro M N f
  have := reductionUnit_epi T R _ p M
  let s := reductionUnit T R _ p
  have hm : s.app M ≫ (ReductionTensor.ordinaryQuotientIso T R φ M).hom =
      (pbcScalarAdjunction φ).unit.app M :=
    ReductionTensor.ordinaryQuotient_unit T R φ p hp M
  have hn : s.app N ≫ (ReductionTensor.ordinaryQuotientIso T R φ N).hom =
      (pbcScalarAdjunction φ).unit.app N :=
    ReductionTensor.ordinaryQuotient_unit T R φ p hp N
  apply (cancel_epi (s.app M)).1
  rw [← Category.assoc, ← s.naturality f]
  change (f ≫ s.app N) ≫ _ = _
  rw [Category.assoc, hn]
  calc
    _ = (pbcScalarAdjunction φ).unit.app M ≫ (pbcExtend φ ⋙ pbcRestrict φ).map f :=
      (pbcScalarAdjunction φ).unit.naturality f
    _ = _ := by rw [← Category.assoc, hm]
private instance tensorLeftSite_zero (B : Mod T R) :
    (tensorLeftSite T R B).PreservesZeroMorphisms where
  map_zero M N := by
    let a := PresheafOfModules.sheafification (𝟙 ((adicLisseForget T).obj R).obj)
    change a.map _ = 0
    rw [← a.map_zero]
    congr 1
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    change x ⊗ₜ[R.obj.obj V] (0 : N.val.obj V) = 0
    simp only [TensorProduct.tmul_zero]
private def tensorComplex (P : CochainComplex (Mod T R) ℤ) (B : Mod T R) :=
  ((tensorLeftSite T R B).mapHomologicalComplex (.up ℤ)).obj P
private def tensorComplexMap (P : CochainComplex (Mod T R) ℤ)
    {B B' : Mod T R} (f : B ⟶ B') : tensorComplex T R P B ⟶ tensorComplex T R P B' :=
  (NatTrans.mapHomologicalComplex (coefficientMap T R f) (.up ℤ)).app P
private theorem tensorComplex_exact (P : CochainComplex (Mod T R) ℤ)
    (S : ShortComplex (Mod T R)) (hs : S.ShortExact)
    (hflat : ∀ i : ℤ, exactFunctor (Mod T R) (Mod T R)
      (siteSheafTensorRight (A := R) (P.X i))) :
    ∃ hz : tensorComplexMap T R P S.f ≫ tensorComplexMap T R P S.g = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  have hz : tensorComplexMap T R P S.f ≫ tensorComplexMap T R P S.g = 0 := by
    apply HomologicalComplex.hom_ext
    intro i
    change (siteSheafTensorRight (P.X i)).map S.f ≫
      (siteSheafTensorRight (P.X i)).map S.g = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero]
  refine ⟨hz, ?_⟩
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  let F := siteSheafTensorRight (A := R) (P.X i)
  let := ((exactFunctor_iff F).1 (hflat i)).1
  let := ((exactFunctor_iff F).1 (hflat i)).2
  exact hs.map_of_exact F
private def tensorComplexIso {S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (φ : R ⟶ S)
    (p : unit ((adicLisseForget T).obj R) ⟶
      (pbcRestrict φ).obj (unit ((adicLisseForget T).obj S))) [Epi p]
    (hp : ∀ V : T.ProEtᵒᵖ, p.val.app V (1 : R.obj.obj V) = (1 : S.obj.obj V))
    (P : CochainComplex (Mod T R) ℤ) :
    tensorComplex T R P ((pbcRestrict φ).obj (unit ((adicLisseForget T).obj S))) ≅
      ((pbcRestrict φ).mapHomologicalComplex (.up ℤ)).obj
        (((pbcExtend φ).mapHomologicalComplex (.up ℤ)).obj P) :=
  (NatIso.mapHomologicalComplex (reductionIso T R φ p hp) (.up ℤ)).app P
end IntegralSuccessorTensorProof

namespace WeilConjectures
attribute [-instance] integralCoefficientAbSheafify integralCoefficientAbLocallyBijective
  integralReductionSiteEssentiallySmall integralReductionSourceHasDerivedCategory
  integralReductionTargetHasDerivedCategory scalarReductionSourceDerived
  scalarReductionTargetDerived integralTowerHasDerivedCategory
  integralCompletedRingHasDerivedCategory
private noncomputable instance fixedSheafify (X : Scheme.{u}) :
    HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} X
private noncomputable instance fixedLocallyBijective (X : Scheme.{u}) :
    (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} X
private instance fixedSmall (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u} _
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  scalarReductionExistence scalarReductionDerivedExistence
  unrestrictedIntegralReductionExistence integralReductionExistence
  integralReductionDerivedExistence

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
private abbrev O : Sheaf (ProEt.topology X) CommRingCat.{u + 1} :=
  completedIntegralCommRingSheafUnrestricted.{u, u} l E X
private abbrev φ (n : ℕ) : O l E X ⟶ integralCoefficientCommRingSheaf.{u, u} l E X n :=
  completedIntegralCommRingProjectionUnrestricted.{u, u} l E X n
private abbrev B (n : ℕ) : integralTowerModules.{u, u} l E X :=
  (SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (φ l E X
      n))).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (integralCoefficientCommRingSheaf.{u, u}
          l E X n)))
private noncomputable def p (n : ℕ) :
    SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (O l E X)) ⟶ B l E X n :=
  IntegralSuccessorProof.coefficientProjection (φ := φ l E X n)
private noncomputable def q (n : ℕ) : B l E X (n + 1) ⟶ B l E X n :=
  IntegralSuccessorProof.coefficientTransition (O := O l E X)
    (S := integralCoefficientCommRingSheaf.{u, u} l E X n) (φ := φ l E X n) (φ' := φ l E X (n + 1))
    (ρ := unrestrictedCoefficientStep.{u, u} l E X n)
    (unrestrictedCoefficientStep_comp.{u, u} l E X n)
private noncomputable def t : (O l E X).obj.obj (op (ProEt.mk (𝟙 X))) :=
  (integralConstantToCompletionOfUniverses.{u, u} l E X).hom.app _
    ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app _
        (ULift.up (Padic.coefficientExtensionUniformizer l E)))
private noncomputable def d : End (SheafOfModules.unit ((sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (O l E X))) :=
  IntegralSuccessorProof.coefficientMultiplication (O := O l E X) (U := ProEt.mk (𝟙 X))
    (hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X) (t := t l E X)
private theorem principalSES (n : ℕ) :
    ∃ hz : (d l E X ^ (n + 1)) ≫ p l E X n = 0,
      (ShortComplex.mk _ _ hz).ShortExact := by
  obtain ⟨hz, hs⟩ := integral_principal_reduction_coefficients X l E n
  have hpower : (d l E X) ^ (n + 1) = IntegralSuccessorProof.coefficientMultiplication
      (O := O l E X) (U := ProEt.mk (𝟙 X))
      (hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X)
      (t := ((integralConstantToCompletionOfUniverses.{u, u} l E X).hom.app _
        ((toSheafify (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))))).app _
            (ULift.up (Padic.coefficientExtensionUniformizer l E) ^ (n + 1))))) := by
    dsimp only [d]
    rw [IntegralSuccessorProof.coefficientMultiplication_pow]
    congr 1
    exact (map_pow _ _ _).symm.trans (congrArg _ (map_pow _ _ _).symm)
  have hs' := IntegralSuccessorProof.coefficient_shortExact (O := O l E X)
    (S := integralCoefficientCommRingSheaf.{u, u} l E X n) (t := _)
    (U := ProEt.mk (𝟙 X)) (hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X)
    (φ := φ l E X n) hz hs
  have hz' : (d l E X ^ (n + 1)) ≫ p l E X n = 0 := by
    rw [hpower]
    exact IntegralSuccessorProof.coefficient_zero (O := O l E X)
      (S := integralCoefficientCommRingSheaf.{u, u} l E X n)
      (U := ProEt.mk (𝟙 X)) (hU := MorphismProperty.Over.mkIdTerminal @WeaklyEtale X)
      (t := _) (φ := φ l E X n) hz
  refine ⟨hz', ?_⟩
  simpa only [hpower, p, B] using hs'
private theorem successorSES (n : ℕ) :
    ∃ i : B l E X 0 ⟶ B l E X (n + 1), ∃ hz : i ≫ q l E X n = 0,
      (ShortComplex.mk i (q l E X n) hz).ShortExact := by
  obtain ⟨h₀, hs₀⟩ := principalSES l E X 0
  obtain ⟨h₁, hs₁⟩ := principalSES l E X n
  obtain ⟨h₂, hs₂⟩ := principalSES l E X (n + 1)
  have hpow : (d l E X ^ (0 + 1)) ≫ (d l E X ^ (n + 1)) =
      d l E X ^ (n + 1 + 1) := by
    rw [← End.mul_def, ← pow_add]
  have h₂' : ((d l E X ^ (0 + 1)) ≫ (d l E X ^ (n + 1))) ≫ p l E X (n + 1) = 0 := by
    rw [hpow]; exact h₂
  have hs₂' : (ShortComplex.mk _ _ h₂').ShortExact := by
    simpa only [hpow] using hs₂
  exact IntegralSuccessorProof.successorCoefficientSequence _ _ _ _ _ h₀ h₁ h₂' hs₀ hs₁ hs₂'
    (q l E X n) (IntegralSuccessorProof.coefficientTransition_projection _ _ _ _ _ _)

private instance p_epi (n : ℕ) : Epi (p l E X n) :=
  (principalSES l E X n).choose_spec.epi_g
private def tensorTowerIso (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ) (n : ℕ) :
    IntegralSuccessorTensorProof.tensorComplex X (O l E X) P (B l E X n) ≅
      integralTowerComplex.{0, u, u} l E X D hl n P := by
  exact IntegralSuccessorTensorProof.tensorComplexIso X (O l E X) (φ l E X n)
    (p l E X n) (fun V ↦ map_one ((φ l E X n).hom.app V).hom) P
private theorem tensorTowerIso_hom_f (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ) (n : ℕ) (i : ℤ) :
    (tensorTowerIso l E X D hl P n).hom.f i =
      (ReductionTensor.ordinaryQuotientIso X (O l E X) (φ l E X n) (P.X i)).hom := rfl
attribute [local irreducible] tensorTowerIso
private theorem tensorTowerIso_unit (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ) (n : ℕ) (i : ℤ) :
    ((IntegralSuccessorTensorProof.reductionUnit X (O l E X) (B l E X n)
      (p l E X n)).app (P.X i)) ≫ ((tensorTowerIso l E X D hl P n).hom.f i) =
        (integralTowerUnit l E X D hl P n).f i := by
  have h := ReductionTensor.ordinaryQuotient_unit X (O l E X) (φ l E X n)
    (p l E X n) (fun V ↦ map_one ((φ l E X n).hom.app V).hom) (P.X i)
  rw [tensorTowerIso_hom_f]
  apply h.trans
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hu := (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.1
  exact (ReductionTensor.ordinaryUnit_apply X (O l E X) (φ l E X n) (P.X i) V x).trans
    (hu n i V x).symm
private theorem tensorTowerIso_transition (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ) (n : ℕ) :
    IntegralSuccessorTensorProof.tensorComplexMap X (O l E X) P (q l E X n) ≫
        (tensorTowerIso l E X D hl P n).hom =
      (tensorTowerIso l E X D hl P (n + 1)).hom ≫
        integralTowerTransition l E X D hl P n := by
  have hcomp : integralTowerUnit l E X D hl P (n + 1) ≫
      integralTowerTransition l E X D hl P n = integralTowerUnit l E X D hl P n := by
    have hu := (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.1
    have ht : integralTowerTransitionCondition l E X D hl P
        (integralTowerTransition l E X D hl P) :=
      (integralTowerMaps_existUnique l E X D hl P).exists.choose_spec.2
    ext i V x
    change (((integralTowerTransition l E X D hl P n).f i).val.app V)
      ((((integralTowerUnit l E X D hl P (n + 1)).f i).val.app V) x) = _
    erw [hu (n + 1) i V x, hu n i V x]
    simpa only [map_one] using ht n i V 1 x
  apply HomologicalComplex.hom_ext
  intro i
  have := IntegralSuccessorTensorProof.reductionUnit_epi X (O l E X)
    (B l E X (n + 1)) (p l E X (n + 1)) (P.X i)
  apply (cancel_epi ((IntegralSuccessorTensorProof.reductionUnit X (O l E X)
    (B l E X (n + 1)) (p l E X (n + 1))).app (P.X i))).1
  change ((ReductionTensor.tensorUnitIso X (O l E X) (P.X i)).inv ≫
    (siteSheafTensorRight (A := O l E X) (P.X i)).map (p l E X (n + 1))) ≫
      (siteSheafTensorRight (A := O l E X) (P.X i)).map (q l E X n) ≫ _ = _
  have hpq : p l E X (n + 1) ≫ q l E X n = p l E X n :=
    IntegralSuccessorProof.coefficientTransition_projection _ _ _ _ _ _
  rw [Category.assoc, ← Functor.map_comp_assoc, hpq]
  have hn := tensorTowerIso_unit l E X D hl P n i
  have hn' := tensorTowerIso_unit l E X D hl P (n + 1) i
  dsimp only [IntegralSuccessorTensorProof.reductionUnit,
    IntegralSuccessorTensorProof.tensorUnitNatural,
    IntegralSuccessorTensorProof.coefficientMap, NatTrans.comp_app] at hn
  rw [← Category.assoc, hn, HomologicalComplex.comp_f, ← Category.assoc, hn']
  exact (congrArg (fun f ↦ f.f i) hcomp).symm

private theorem flatTower_triangle (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ)
    (hflat : ∀ i : ℤ, exactFunctor _ _
      (siteSheafTensorRight (A := O l E X) (P.X i))) (n : ℕ) :
    ∃ (ι : DerivedCategory.Q.obj (integralTowerComplex l E X D hl 0 P) ⟶
      DerivedCategory.Q.obj (integralTowerComplex l E X D hl (n + 1) P))
      (δ : DerivedCategory.Q.obj (integralTowerComplex l E X D hl n P) ⟶
        (DerivedCategory.Q.obj (integralTowerComplex l E X D hl 0 P))⟦(1 : ℤ)⟧),
      Triangle.mk ι (DerivedCategory.Q.map (integralTowerTransition l E X D hl P n)) δ ∈
        distTriang (completedIntegralDerivedCategory.{0, u, u} l E X D hl) := by
  obtain ⟨i, hz, hs⟩ := successorSES l E X n
  let S := ShortComplex.mk i (q l E X n) hz
  obtain ⟨hz', hs'⟩ := IntegralSuccessorTensorProof.tensorComplex_exact X (O l E X) P S hs hflat
  let e₀ := tensorTowerIso l E X D hl P 0
  let e₁ := tensorTowerIso l E X D hl P (n + 1)
  let e₂ := tensorTowerIso l E X D hl P n
  let f := e₀.inv ≫ IntegralSuccessorTensorProof.tensorComplexMap X (O l E X) P i ≫ e₁.hom
  let g := integralTowerTransition l E X D hl P n
  have he : e₁.hom ≫ g =
      IntegralSuccessorTensorProof.tensorComplexMap X (O l E X) P (q l E X n) ≫ e₂.hom :=
    (tensorTowerIso_transition l E X D hl P n).symm
  have hz'' : f ≫ g = 0 := by
    dsimp only [f]
    rw [Category.assoc, Category.assoc, he, ← Category.assoc _ _ e₂.hom,
      hz', zero_comp, comp_zero]
  let S' := ShortComplex.mk f g hz''
  have hs'' : S'.ShortExact := by
    apply (ShortComplex.shortExact_iff_of_iso
      (ShortComplex.isoMk e₀ e₁ e₂ (by simp [S', f, S]) he)).1 hs'
  exact ⟨DerivedCategory.Q.map f, DerivedCategory.triangleOfSESδ hs'',
    DerivedCategory.triangleOfSES_distinguished hs''⟩

/-- Consecutive reductions have the residue reduction as their homotopy fibre.

Source: Stacks Project, sites-cohomology.tex, Tag 0942, lemma-bounded, coefficient
filtration argument; Tags 06YN/06YP, tensoring with a K-flat complex; derived.tex,
Tag 0152, the distinguished triangle of a short exact sequence.
(blueprint: lem-sf-integral-reduction-successor-triangle).

Proof: write R for the valuation ring, pi for its nonzero uniformizer, and
C_m for the constant sheaf R/pi^(m+1), with its action through the fixed completed
ring projection. The coefficient sequence 0 -> C_0 -> C_(n+1) -> C_n -> 0 is
short exact. Its first map sends the class of r to the class of pi^(n+1)r.
Cancellation in the DVR proves injectivity and identifies its image with the kernel
of the quotient map. Sheafification is exact on underlying additive sheaves. The
maps are linear over the completed ring: its projections to C_(n+1) and C_0 agree
after reduction, so their actions on pi^(n+1)r coincide. Tensor this coefficient
sequence with P in the derived category. K-flatness identifies the resulting
objects with the localized termwise scalar extensions in the statement. For an
explicit construction, resolve P by a K-flat complex with flat terms, tensor the
coefficient sequence degreewise, and apply the short-exact-sequence triangle.
The comparison with P is a quasi-isomorphism at every level by K-flat tensor
invariance and is natural for coefficient maps. Thus the second map is precisely
the localization of integralTowerTransition, whose pure-tensor formula is
s tensor x mapped to residue(s) tensor x. Transport the triangle through these
comparisons, retaining that second map. This argument works also for n=0, zero
complexes, and the empty scheme. -/
theorem integralReduction_successor_triangle
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) (D : FiniteFieldDatum.{0}) (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules.{u, u} l E X) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{u} X.ProEt) (ProEt.topology X)
      (completedIntegralCommRingSheafUnrestricted.{u, u} l E X) P) (n : ℕ) :
    let F := integralReductionTower.{0, u, u} l E X D hl P
    ∃ (ι : F.obj (op 0) ⟶ F.obj (op (n + 1)))
      (δ : F.obj (op n) ⟶ (F.obj (op 0))⟦(1 : ℤ)⟧),
      Triangle.mk ι (F.map (homOfLE n.le_succ).op) δ ∈
        distTriang (completedIntegralDerivedCategory.{0, u, u} l E X D hl) := by
  classical
  let := SheafOfModules.isMonoidal_W_independentCoefficients (O l E X)
  let := SheafOfModules.monoidalCategory (O l E X)
  obtain ⟨Q, r, hQ, hflat, hr, _⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients (R := O l E X) P
  have hflat' (i : ℤ) : exactFunctor _ _
      (siteSheafTensorRight (A := O l E X) (Q.X i)) :=
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso (O l E X) (Q.X i)).symm (hflat i)
  obtain ⟨ι, δ, hd⟩ := flatTower_triangle l E X D hl Q hflat' n
  have hr' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := O l E X) r := ⟨hr, hQ⟩
  have hid : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (R := O l E X) (𝟙 P) := ⟨inferInstance, hP⟩
  let e (m : ℕ) := integralTowerComparison l E X D hl m r (𝟙 P) hr' hid
  have he := (integralReductionTowerWellDefined l E X D hl r (𝟙 P) hr' hid).2 n
  change DerivedCategory.Q.map (integralTowerTransition l E X D hl Q n) ≫ (e n).hom =
    (e (n + 1)).hom ≫ DerivedCategory.Q.map (integralTowerTransition l E X D hl P n) at he
  let ι' := (e 0).inv ≫ ι ≫ (e (n + 1)).hom
  let δ' := (e n).inv ≫ δ ≫ (e 0).hom⟦(1 : ℤ)⟧'
  refine ⟨ι', δ', ?_⟩
  simp only [integralReductionTower, Functor.ofOpSequence_map_homOfLE_succ]
  apply isomorphic_distinguished _ hd _
  refine Triangle.isoMk _ _ (e 0).symm (e (n + 1)).symm (e n).symm ?_ ?_ ?_
  · simp [ι']
  · change DerivedCategory.Q.map (integralTowerTransition l E X D hl P n) ≫ (e n).inv =
      (e (n + 1)).inv ≫ DerivedCategory.Q.map (integralTowerTransition l E X D hl Q n)
    apply (cancel_mono (e n).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.inv_hom_id_assoc] using congrArg (fun f ↦ (e (n + 1)).inv ≫ f) he.symm
  · simp only [δ', Triangle.mk_mor₃, Iso.symm_hom, Category.assoc]
    change (e n).inv ≫ δ ≫
      (shiftFunctor (completedIntegralDerivedCategory.{0, u, u} l E X D hl) (1 : ℤ)).map
        (e 0).hom ≫
      (shiftFunctor (completedIntegralDerivedCategory.{0, u, u} l E X D hl) (1 : ℤ)).map
        (e 0).inv = (e n).inv ≫ δ
    rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    exact congrArg (fun f ↦ (e n).inv ≫ f) (Category.comp_id δ)

end WeilConjectures
