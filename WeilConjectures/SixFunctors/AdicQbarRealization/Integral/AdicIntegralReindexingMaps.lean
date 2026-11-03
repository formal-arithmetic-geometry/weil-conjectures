/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.AdicRealizationFamilyData
import all WeilConjectures.AlgebraicGeometry.SixFunctors.LimitScalarChainComparison
import all WeilConjectures.CategoryTheory.Exact.ExactEquivalenceDerivedSquares
import all WeilConjectures.SmoothPurity.Supporting.IsomorphismReductionTower
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement

/-! # Integral reindexing maps for one native realization comparison

This is the map-construction part of the common-stage integral descent argument.
Source: Bhatt--Scholze, Remark 6.8.15; Hemo--Richarz--Scholbach, Lemma 7.9.
(blueprint: lem-sf-adic-integral-reindexing-maps)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

attribute [local irreducible] scalarSquareIso
attribute [-instance] isoReductionSiteSmall

private theorem completed_presentation_natural
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    (A : Type u) [Field A] [Algebra (Padic l) A] [FiniteDimensional (Padic l) A]
    (i : A →ₐ[Padic l] PadicAlgCl l)
    (C : letI := R.commutative
      LocallyFiniteAdicRealization.CoefficientPresentation l X A i)
    (D : letI := S.commutative
      LocallyFiniteAdicRealization.CoefficientPresentation l Y A i) :
    letI := R.commutative
    letI := S.commutative
    let HX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let HY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let F := isoSectionwiseInverseImage g RingCat.{u + 1}
    F.map (HY.map D.integral.hom) ≫ podCompletedRingMap l A g =
      HX.map C.integral.hom := by
  let := R.commutative
  let := S.commutative
  let HX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let HY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  have hfinite (n : ℕ) :
      F.map (HY.map (D.finite n).hom) =
        isoSectionwiseConstantMap.{u, u} g (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n) ≫
          HX.map (C.finite n).hom := by
    let f := F.map (HY.map (D.finite n).hom) ≫ HX.map (C.finite n).inv
    have hf : f = isoSectionwiseConstantMap.{u, u} g
        (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n) := by
      have hconst := isoSectionwiseConstantMap_existsUnique.{u, u} g
        (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n)
      refine hconst.unique ?_ hconst.exists.choose_spec
      intro U a
      apply (ConcreteCategory.bijective_of_isIso
        ((C.finite n).hom.hom.app (op U))).1
      have hi := congrArg (fun h ↦ h.hom.app (op U)) (C.finite n).inv_hom_id
      change (C.finite n).inv.hom.app (op U) ≫
        (C.finite n).hom.hom.app (op U) = 𝟙 _ at hi
      change (C.finite n).hom.hom.app (op U)
          ((C.finite n).inv.hom.app (op U)
            ((D.finite n).hom.hom.app (op ((proEtaleIsoPostcompose g).obj U)) _)) = _
      erw [← ConcreteCategory.comp_apply, hi]
      apply @ContinuousMap.ext U.left (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n) _ ⊥
      intro x
      exact (D.finite_constants n (op ((proEtaleIsoPostcompose g).obj U)) a x).trans
        (C.finite_constants n (op U) a x).symm
    calc
      _ = f ≫ HX.map (C.finite n).hom := by
        dsimp only [f]
        erw [Category.assoc, ← HX.map_comp, Iso.inv_hom_id, HX.map_id, Category.comp_id]
      _ = _ := by erw [hf]; rfl
  apply limit.hom_ext
  intro n
  change (F.map (HY.map D.integral.hom) ≫ podCompletedRingMap l A g) ≫
      limit.π (integralCoefficientSheafSystem l A X) n =
    HX.map C.integral.hom ≫ limit.π (integralCoefficientSheafSystem l A X) n
  erw [Category.assoc]
  unfold podCompletedRingMap
  erw [limit.lift_π]
  change F.map (HY.map D.integral.hom) ≫
      (F.map (limit.π (integralCoefficientSheafSystem l A Y) n) ≫
        isoSectionwiseConstantMap.{u, u} g
          (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n.unop)) = _
  erw [← Category.assoc, ← F.map_comp]
  apply (cancel_mono (HX.map (C.finite n.unop).hom)).1
  erw [Category.assoc, ← hfinite, ← F.map_comp]
  change F.map (HY.map (D.integral.hom ≫
      completedIntegralCommRingProjectionUnrestricted l A Y n.unop ≫
        (D.finite n.unop).hom)) =
    HX.map (C.integral.hom ≫
      completedIntegralCommRingProjectionUnrestricted l A X n.unop ≫
        (C.finite n.unop).hom)
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  apply @ContinuousMap.ext U.unop.left
    (AlgebraicGeometry.Scheme.finiteCoefficientRing l A n.unop) _ ⊥
  intro x
  apply ULift.ext
  exact (D.integral_residues n.unop ((proEtaleIsoPostcompose g).op.obj U) s x).trans
    (C.integral_residues n.unop U s x).symm

private theorem coefficient_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    let HX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let HY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    let F := isoSectionwiseInverseImage g RingCat.{u + 1}
    F.map (HY.map (coefficientMap l Y S E)) ≫ (HX.mapIso B.iso).hom =
      podCompletedRingMap l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ≫
        HX.map (coefficientMap l X R E) := by
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let := R.commutative
  let := S.commutative
  let C := R.coefficient E
  let D := S.coefficient E
  let HX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let HY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  have hcompletion : F.map (HY.map D.integral.hom) ≫ podCompletedRingMap l A g =
      HX.map C.integral.hom :=
    completed_presentation_natural l g R S A (LocallyFiniteAdicRealization.embedding l E) C D
  change F.map (HY.map (coefficientMap l Y S E)) ≫ HX.map B.iso.hom =
    podCompletedRingMap l A g ≫ HX.map (coefficientMap l X R E)
  apply (cancel_epi (F.map (HY.map D.integral.hom))).1
  refine Eq.trans ?_
    ((congrArg (fun f ↦ f ≫ HX.map (coefficientMap l X R E)) hcompletion.symm).trans
      (Category.assoc _ _ _))
  change F.map (HY.map D.integral.hom) ≫
      F.map (HY.map (D.integral.inv ≫ D.integralInclusion ≫ D.rationalInclusion)) ≫
        HX.map B.iso.hom =
      HX.map C.integral.hom ≫
        HX.map (C.integral.inv ≫ C.integralInclusion ≫ C.rationalInclusion)
  erw [← F.map_comp_assoc, ← HY.map_comp, Iso.hom_inv_id_assoc,
    ← HX.map_comp, Iso.hom_inv_id_assoc]
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply RingCat.hom_ext
  apply RingHom.ext
  intro s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change (B.iso.hom.hom.app U
      (D.rationalInclusion.hom.app ((proEtaleIsoPostcompose g).op.obj U)
        (D.integralInclusion.hom.app ((proEtaleIsoPostcompose g).op.obj U) s))).down.1 x =
    (C.rationalInclusion.hom.app U (C.integralInclusion.hom.app U s)).down.1 x
  erw [B.functions]
  erw [D.rationalInclusion_normalized, C.rationalInclusion_normalized]
  exact congrArg (LocallyFiniteAdicRealization.embedding l E)
    ((D.integralInclusion_normalized ((proEtaleIsoPostcompose g).obj U.unop) s x).trans
      (C.integralInclusion_normalized U.unop s x).symm)

private def restriction_square
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    pbcRestrict (coefficientMap l Y S E) ⋙
        podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ≅
      modulePull l X g B ⋙ pbcRestrict (coefficientMap l X R E) := by
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let HX := sheafCompose (ProEt.topology X) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let HY := sheafCompose (ProEt.topology Y) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let F := isoSectionwiseInverseImage g RingCat.{u + 1}
  let cR := podCompletedRingMap l A g
  let cS := (HX.mapIso B.iso).hom
  have hi : inv cR ≫ F.map (HY.map (coefficientMap l Y S E)) =
      HX.map (coefficientMap l X R E) ≫ inv cS := by
    apply (cancel_mono cS).1
    erw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    erw [coefficient_square l g R S B E, IsIso.inv_hom_id_assoc]
  refine NatIso.ofComponents (fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun U ↦ LinearEquiv.toModuleIso
        (m₁ := (((pbcRestrict (coefficientMap l Y S E) ⋙
          podCompletedModuleInverseImage l A g).obj M).val.obj U).isModule)
        (m₂ := (((modulePull l X g B ⋙
          pbcRestrict (coefficientMap l X R E)).obj M).val.obj U).isModule)
        { toFun := fun x ↦ x
          invFun := fun x ↦ x
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          map_smul' := ?_ }) (fun _ _ f ↦ by ext x; rfl))) (fun f ↦ by ext U x; rfl)
  intro r x
  let y : M.val.obj ((proEtaleIsoPostcompose g).op.obj U) := x
  let act (z : (HY.obj (ring l Y S)).obj.obj
      ((proEtaleIsoPostcompose g).op.obj U)) : M.val.obj
        ((proEtaleIsoPostcompose g).op.obj U) := z • y
  change act ((coefficientMap l Y S E).hom.app ((proEtaleIsoPostcompose g).op.obj U)
      ((inv cR).hom.app U r)) =
    act ((inv cS).hom.app U ((coefficientMap l X R E).hom.app U r))
  exact congrArg act (congrArg (fun f ↦ f.hom.app U r) hi)

private theorem native_pull_equivalence
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S) :
    (modulePull l X g B).IsEquivalence := by
  have hB : IsIso (((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom) :=
    (Functor.mapIso _ B.iso).isIso_hom
  unfold modulePull
  refine @isoReduction_equivalence.{u, u} X Y g _ _ _ _ ?_

private theorem ordinary_balance_exists
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    ∃ balance : pbcExtend.{u} (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
        podCompletedModuleInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
          pbcExtend.{u} (coefficientMap l X R E),
      integralReindexSections l X g B E balance := by
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let F := podCompletedModuleInverseImage l A g
  let G := modulePull l X g B
  let a := pbcScalarAdjunction (coefficientMap l Y S E)
  let a' := pbcScalarAdjunction (coefficientMap l X R E)
  let e := restriction_square l g R S B E
  have : F.IsEquivalence := isoReduction_equivalence.{u, u} g (podCompletedRingMap l A g)
  have : G.IsEquivalence := native_pull_equivalence l g R S B
  let b := scalarSquareIso F G a a' e
  refine ⟨b.symm, ?_⟩
  intro M U s x
  have hunit := congrArg (fun h ↦ h.val.app U x)
    (scalarSquareIso_unit F G a a' e M)
  have hx : (b.hom.app M).val.app U
      (pbcTensorSection (coefficientMap l X R E) (F.obj M) U 1 x) =
        pbcTensorSection (coefficientMap l Y S E) M
          ((proEtaleIsoPostcompose g).op.obj U) 1 x := by
    change (b.hom.app M).val.app U ((a'.unit.app (F.obj M)).val.app U x) = _ at hunit
    have huX : (a'.unit.app (F.obj M)).val.app U x =
        pbcTensorSection (coefficientMap l X R E) (F.obj M) U 1 x :=
      (pbcScalarAdjunction_exists (coefficientMap l X R E)).exists.choose_spec _ _ _
    erw [huX] at hunit
    change _ = ((a.unit.app M).val.app ((proEtaleIsoPostcompose g).op.obj U) x) at hunit
    have huY : (a.unit.app M).val.app ((proEtaleIsoPostcompose g).op.obj U) x =
        pbcTensorSection (coefficientMap l Y S E) M
          ((proEtaleIsoPostcompose g).op.obj U) 1 x :=
      (pbcScalarAdjunction_exists (coefficientMap l Y S E)).exists.choose_spec _ _ _
    erw [huY] at hunit
    exact hunit
  have hp : (b.hom.app M).val.app U
      (pbcTensorSection (coefficientMap l X R E) (F.obj M) U
        (B.iso.hom.hom.app U s) x) =
      pbcTensorSection (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj U) s x := by
    dsimp only [pbcTensorSection] at hx ⊢
    have smulX := completedTensor_smul X (coefficientMap l X R E) (F.obj M)
      U (B.iso.hom.hom.app U s) 1 x
    have smulY := completedTensor_smul Y (coefficientMap l Y S E) M
      ((proEtaleIsoPostcompose g).op.obj U) s 1 x
    erw [mul_one] at smulX smulY
    erw [smulX, (b.hom.app M).val.app U |>.hom.map_smul, hx]
    let cS := ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso B.iso).hom
    let act (a : ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (ring l Y S)).obj.obj
          ((proEtaleIsoPostcompose g).op.obj U)) :
        ((pbcExtend (coefficientMap l Y S E)).obj M).val.obj
          ((proEtaleIsoPostcompose g).op.obj U) :=
      a • completedAdicChangeTensor Y (coefficientMap l Y S E) M
        ((proEtaleIsoPostcompose g).op.obj U) 1 x
    change act ((inv cS).hom.app U (B.iso.hom.hom.app U s)) = _
    have hc := congrArg (fun h ↦ h.hom.app U s) (IsIso.hom_inv_id cS)
    change (inv cS).hom.app U (B.iso.hom.hom.app U s) = s at hc
    erw [hc]
    exact smulY.symm
  have hcancel := congrArg (fun h ↦ h.val.app U
    (pbcTensorSection (coefficientMap l X R E) (F.obj M) U
      (B.iso.hom.hom.app U s) x)) (b.app M).hom_inv_id
  exact (congrArg ((b.inv.app M).val.app U) hp.symm).trans hcancel

attribute [local irreducible] pbcExtensionCounit coefficientMap

private theorem derived_balance_exists
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (balance : pbcExtend (coefficientMap l Y S E) ⋙ modulePull l X g B ≅
      podCompletedModuleInverseImage l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
        pbcExtend (coefficientMap l X R E)) :
    ∃ derived : pbcDerivedExtend (coefficientMap l Y S E) ⋙ derivedPull l X g B ≅
        podCompletedDerivedInverseImage l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g ⋙
          pbcDerivedExtend (coefficientMap l X R E),
      integralReindexRepresentative l X g B E balance derived := by
  let : EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : EssentiallySmall.{u + 1} Y.ProEt := essentiallySmallSelf.{0, u, u + 1} _
  let : HasSheafify (ProEt.topology X) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} X
  let : HasSheafify (ProEt.topology Y) AddCommGrpCat.{u + 1} :=
    integralCoefficientAbSheafify.{u, 0} Y
  let : (ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} X
  let : (ProEt.topology Y).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    integralCoefficientAbLocallyBijective.{u, 0} Y
  let A := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let F := podCompletedModuleInverseImage l A g
  let G := modulePull l X g B
  let jY := coefficientMap l Y S E
  let jX := coefficientMap l X R E
  have : F.IsEquivalence := isoReduction_equivalence.{u, u} g (podCompletedRingMap l A g)
  have : G.IsEquivalence := native_pull_equivalence l g R S B
  let cY := derivedCochainCounit.{u + 1, u + 2, u + 1, u + 2, u + 2, u + 2}
    (pbcExtend.{u} jY) (pbcDerivedExtend.{u} jY)
    (pbcExtensionCounit.{u} jY)
  let cX := derivedCochainCounit.{u + 1, u + 2, u + 1, u + 2, u + 2, u + 2}
    (pbcExtend.{u} jX) (pbcDerivedExtend.{u} jX)
    (pbcExtensionCounit.{u} jX)
  let := pbcDerivedExtension_universal.{u} jY
  let := pbcDerivedExtension_universal.{u} jX
  have : (pbcDerivedExtend.{u} jY).IsRightKanExtension cY :=
    cochainCounit_universal _ _ _
  have : (pbcDerivedExtend.{u} jX).IsRightKanExtension cX :=
    cochainCounit_universal _ _ _
  have : F.asEquivalence.functor.Additive := podCompletedModuleAdditive l A g
  have : G.asEquivalence.functor.Additive := modulePullAdditive l X g B
  obtain ⟨derived, hderived⟩ := leftDerivedSquare F.asEquivalence G.asEquivalence
    (pbcExtend.{u} jY) (pbcExtend.{u} jX) (pbcDerivedExtend.{u} jY) (pbcDerivedExtend.{u} jX)
    cY cX balance
  refine ⟨derived, ?_⟩
  intro P
  have hcY : cY.app P = pbcComplexCounit.{u} jY P := by
    simp [cY, derivedCochainCounit, derivedCochainComparisonFactors, pbcComplexCounit]
  have hcX : cX.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      pbcComplexCounit.{u} jX ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    simp [cX, derivedCochainCounit, derivedCochainComparisonFactors, pbcComplexCounit]
  dsimp only [CategoryTheory.Equivalence.mapDerivedCategory,
    CategoryTheory.Equivalence.mk, CategoryTheory.Functor.asEquivalence] at hderived
  have hd := hderived P
  simp only [hcY, hcX, CategoryTheory.Functor.comp_obj,
    G, F, jY, jX, A] at hd
  convert hd using 0
  rfl

private theorem integral_reindex_nonempty
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g]
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y) (B : RingReindex l X g R S)
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l)) :
    Nonempty (IntegralReindex l X g B E) := by
  obtain ⟨balance, hsections⟩ := ordinary_balance_exists l g R S B E
  obtain ⟨derived, hderived⟩ := derived_balance_exists l g R S B E balance
  exact ⟨⟨balance, hsections, derived, hderived⟩⟩

/--
The balanced integral reindexing maps exist for every finite coefficient field.
The proof compares the finite quotient projections of the completed coefficient
sheaves, then localizes the resulting cochain comparison. It uses the coefficient
cartesian and finite-colimit statements, and the exact inverse-image tensor/Hom
comparison. The same construction works for identity and inverse scheme
isomorphisms and for zero complexes; no common-stage comparison is asserted here.
 (blueprint: lem-sf-adic-integral-reindexing-maps)
-/
theorem exists_integral_reindexing_maps (D : FiniteFieldDatum.{u})
    (d : ∀ T : GeometricSpace D, SpaceData l D T)
    (T U : GeometricSpace D) (g : T.base.left ≅ U.base.left)
    (B : RingReindex l T.base.left g.hom (d T).realization (d U).realization) :
    letI := (d T).units
    letI := (d U).units
    Nonempty (∀ E, IntegralReindex l T.base.left g.hom B E) := by
  exact ⟨fun E ↦ (integral_reindex_nonempty l g.hom
    (d T).realization (d U).realization B E).some⟩

end WeilConjectures.AdicQbarRealization
