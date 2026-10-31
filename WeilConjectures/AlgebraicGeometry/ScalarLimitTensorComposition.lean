/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
import all WeilConjectures.CategoryTheory.DerivedExactSquareCoherence

/-! # Coherence of the normalized tensor and arithmetic limit comparisons

Source: Stacks Tag 0941; auxiliary Step 7 of strict compact-support scalar composition.
(blueprint: lem-pur-scalar-limit-tensor-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
attribute [local irreducible] HasDerivedCategory.standard
attribute [local irreducible] WeilConjectures.PurStrictScalar.scalarLimitTensor
  WeilConjectures.PurStrictScalar.scalarLimitRestriction
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

private theorem factorsh_quotient
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv,
    Quotient.lift.isLift_hom]
  erw [CategoryTheory.Functor.map_id, DerivedCategory.Qh.map_id]
  erw [Category.comp_id, Category.comp_id, Category.id_comp]

section SquareHelpers

variable {A B Ap Bp : Type (u + 1)}
  [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
  [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory Ap] [HasDerivedCategory Bp]
  [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions Ap]
  (H : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
  [H.Additive] [G.Additive] [x.Additive] [y.Additive]
  [PreservesFiniteLimits x] [PreservesFiniteColimits x]
  [PreservesFiniteLimits y] [PreservesFiniteColimits y]
  [x.PreservesKInjectiveComplexes]

private theorem tensorSquare_normalized (c : H ⋙ y ≅ x ⋙ G) :
    ExactDerivedSquare.unitNormalized H G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c.hom
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso H y).symm ≪≫
        Functor.rightDerivedFunctorNatIso c ≪≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorIso x G).hom := by
  intro I
  let P := (HomotopyCategory.quotient A (.up ℤ)).obj I
  have hstart : y.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app P) =
      y.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj P) ≫
        (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit H y).app P := by
    have hi : (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (H ⋙ y)) (.up ℤ)).inv.app P = 𝟙 _ := rfl
    simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, hi, Category.id_comp, Category.comp_id]
    erw [DerivedCategory.Qh.map_id, Category.id_comp, Iso.hom_inv_id_app_assoc]
  have hnorm : y.mapDerivedCategory.map (H.rightDerivedFunctorUnit.app P) ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso H y).symm ≪≫
        Functor.rightDerivedFunctorNatIso c ≪≫
        Functor.mapDerivedCategoryCompRightDerivedFunctorIso x G).hom.app
          (DerivedCategory.Qh.obj P) ≫
      G.rightDerivedFunctor.map (x.mapDerivedCategoryFactorsh.hom.app P) =
    y.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P) ≫
      G.rightDerivedFunctorUnit.app ((x.mapHomotopyCategory (.up ℤ)).obj P) := by
    rw [hstart]
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
      Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
      Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
      Iso.refl_inv, Iso.refl_hom]
    rw [Functor.rightDerivedNatTrans_app_assoc]
    simp only [NatTrans.id_app, Category.id_comp]
    rw [Functor.rightDerivedNatTrans_app_assoc]
    simp only [Functor.whiskerRight_app]
    rw [Functor.mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app_assoc]
    have hi : (Functor.mapHomotopyCategoryCompIso
        (Iso.refl (x ⋙ G)) (.up ℤ)).inv.app P = 𝟙 _ := rfl
    simp only [Functor.mapDerivedCategoryCompRightDerivedFunctorUnit_app, hi]
    erw [DerivedCategory.Qh.map_id, Category.id_comp]
    simp only [Category.assoc]
    erw [← G.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
      G.rightDerivedFunctor.map_id, Category.comp_id]
  simp only [Functor.mapHomotopyCategory_obj, HomotopyCategory.quotient_obj_as, P] at hnorm
  rw [factorsh_quotient, factorsh_quotient] at hnorm
  have hc : DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app I) := by
    exact DerivedCategory.Q.congr_map (by rfl)
  rw [hc] at hnorm
  simp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  erw [H.rightDerivedFunctor.map_id, G.rightDerivedFunctor.map_id]
  erw [Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id]
  exact hnorm

end SquareHelpers

private theorem compositeFactors
    {C D V : Type*} [Category C] [Category D] [Category V]
    [Abelian C] [Abelian D] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory V]
    (f : C ⥤ D) (g : D ⥤ V) (h : C ⥤ V)
    [f.Additive] [g.Additive] [h.Additive]
    [PreservesFiniteLimits f] [PreservesFiniteColimits f]
    [PreservesFiniteLimits g] [PreservesFiniteColimits g]
    [PreservesFiniteLimits h] [PreservesFiniteColimits h]
    (a : f ⋙ g ≅ h) (I : CochainComplex C ℤ) :
    ((Functor.mapDerivedCategoryCompIso f g).symm ≪≫
        Functor.mapDerivedCategoryNatIso a).hom.app (DerivedCategory.Q.obj I) ≫
        h.mapDerivedCategoryFactors.hom.app I =
      g.mapDerivedCategory.map (f.mapDerivedCategoryFactors.hom.app I) ≫
        g.mapDerivedCategoryFactors.hom.app ((f.mapHomologicalComplex (.up ℤ)).obj I) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex a.hom (.up ℤ)).app I) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso f g).hom.app
    (DerivedCategory.Q.obj I))).mp
  simp only [Iso.hom_inv_id_app_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

section Horizontal

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type (u + 1)}
  [Category.{u} A₀] [Category.{u} A₁] [Category.{u} A₂]
  [Category.{u} B₀] [Category.{u} B₁] [Category.{u} B₂]
  [Abelian A₀] [Abelian A₁] [Abelian A₂]
  [Abelian B₀] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  [Abelian.HasKInjectiveResolutions A₀] [Abelian.HasKInjectiveResolutions A₁]
  [Abelian.HasKInjectiveResolutions A₂]
  (H₀ : A₀ ⥤ B₀) (H₁ : A₁ ⥤ B₁) (H₂ : A₂ ⥤ B₂)
  (x₁ : A₀ ⥤ A₁) (x₂ : A₁ ⥤ A₂) (x₃ : A₀ ⥤ A₂)
  (y₁ : B₀ ⥤ B₁) (y₂ : B₁ ⥤ B₂) (y₃ : B₀ ⥤ B₂)
  [H₀.Additive] [H₁.Additive] [H₂.Additive]
  [x₁.Additive] [x₂.Additive] [x₃.Additive]
  [y₁.Additive] [y₂.Additive] [y₃.Additive]
  [PreservesFiniteLimits x₁] [PreservesFiniteColimits x₁]
  [PreservesFiniteLimits x₂] [PreservesFiniteColimits x₂]
  [PreservesFiniteLimits x₃] [PreservesFiniteColimits x₃]
  [PreservesFiniteLimits y₁] [PreservesFiniteColimits y₁]
  [PreservesFiniteLimits y₂] [PreservesFiniteColimits y₂]
  [PreservesFiniteLimits y₃] [PreservesFiniteColimits y₃]

private theorem normalized_horizontal
    (c₁ : H₀ ⋙ y₁ ≅ x₁ ⋙ H₁) (c₂ : H₁ ⋙ y₂ ≅ x₂ ⋙ H₂)
    (c₃ : H₀ ⋙ y₃ ≅ x₃ ⋙ H₂)
    (b₁ : H₀.rightDerivedFunctor ⋙ y₁.mapDerivedCategory ≅
      x₁.mapDerivedCategory ⋙ H₁.rightDerivedFunctor)
    (b₂ : H₁.rightDerivedFunctor ⋙ y₂.mapDerivedCategory ≅
      x₂.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (b₃ : H₀.rightDerivedFunctor ⋙ y₃.mapDerivedCategory ≅
      x₃.mapDerivedCategory ⋙ H₂.rightDerivedFunctor)
    (hn₁ : ExactDerivedSquare.unitNormalized H₀ H₁ x₁ y₁
      x₁.mapDerivedCategory y₁.mapDerivedCategory
      x₁.mapDerivedCategoryFactors y₁.mapDerivedCategoryFactors c₁.hom b₁.hom)
    (hn₂ : ExactDerivedSquare.unitNormalized H₁ H₂ x₂ y₂
      x₂.mapDerivedCategory y₂.mapDerivedCategory
      x₂.mapDerivedCategoryFactors y₂.mapDerivedCategoryFactors c₂.hom b₂.hom)
    (hn₃ : ExactDerivedSquare.unitNormalized H₀ H₂ x₃ y₃
      x₃.mapDerivedCategory y₃.mapDerivedCategory
      x₃.mapDerivedCategoryFactors y₃.mapDerivedCategoryFactors c₃.hom b₃.hom)
    (a : x₁ ⋙ x₂ ≅ x₃) (d : y₁ ⋙ y₂ ≅ y₃)
    (hc : ∀ M : A₀, d.hom.app (H₀.obj M) ≫ c₃.hom.app M =
      y₂.map (c₁.hom.app M) ≫ c₂.hom.app (x₁.obj M) ≫ H₂.map (a.hom.app M))
    (K : DerivedCategory A₀) :
    ((Functor.mapDerivedCategoryCompIso y₁ y₂).symm ≪≫
        Functor.mapDerivedCategoryNatIso d).hom.app (H₀.rightDerivedFunctor.obj K) ≫
        b₃.hom.app K =
      y₂.mapDerivedCategory.map (b₁.hom.app K) ≫
        b₂.hom.app (x₁.mapDerivedCategory.obj K) ≫ H₂.rightDerivedFunctor.map
          (((Functor.mapDerivedCategoryCompIso x₁ x₂).symm ≪≫
            Functor.mapDerivedCategoryNatIso a).hom.app K) := by
  let xf := Functor.isoWhiskerRight x₁.mapDerivedCategoryFactors x₂.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (x₁.mapHomologicalComplex (.up ℤ)) x₂.mapDerivedCategoryFactors
  let yf := Functor.isoWhiskerRight y₁.mapDerivedCategoryFactors y₂.mapDerivedCategory ≪≫
    Functor.isoWhiskerLeft (y₁.mapHomologicalComplex (.up ℤ)) y₂.mapDerivedCategoryFactors
  have h := ExactDerivedSquare.normalized_naturality H₀ H₂ (x₁ ⋙ x₂) (y₁ ⋙ y₂) x₃ y₃
    (x₁.mapDerivedCategory ⋙ x₂.mapDerivedCategory) x₃.mapDerivedCategory
    (y₁.mapDerivedCategory ⋙ y₂.mapDerivedCategory) y₃.mapDerivedCategory
    xf x₃.mapDerivedCategoryFactors yf y₃.mapDerivedCategoryFactors
    (Functor.whiskerRight c₁.hom y₂ ≫ Functor.whiskerLeft x₁ c₂.hom) c₃.hom
    (Functor.whiskerRight b₁.hom y₂.mapDerivedCategory ≫
      Functor.whiskerLeft x₁.mapDerivedCategory b₂.hom) b₃.hom
    (ExactDerivedSquare.normalized_comp H₀ H₁ x₁ y₁ H₂ x₂ y₂
      c₁ c₂ b₁ b₂ hn₁ hn₂) hn₃ a.hom d.hom
    ((Functor.mapDerivedCategoryCompIso x₁ x₂).symm ≪≫
      Functor.mapDerivedCategoryNatIso a).hom
    ((Functor.mapDerivedCategoryCompIso y₁ y₂).symm ≪≫
      Functor.mapDerivedCategoryNatIso d).hom
    (fun I ↦ by simpa only [xf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using
        compositeFactors x₁ x₂ x₃ a I)
    (fun I ↦ by simpa only [yf, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using
        compositeFactors y₁ y₂ y₃ d I)
    (fun M ↦ by simpa only [NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hc M)
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using congr_app h K

end Horizontal

namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- The canonical finite-free tensor/limit maps preserve an ordinary tensor comparison.
Source: Stacks Tag 0941; horizontal Roos comparison coherence, auxiliary Step 7 of
compact-support strict scalar composition.
(blueprint: lem-pur-scalar-limit-tensor-composition).
Proof: on strict complexes use the tensor/product comparison in each of the two
Roos coordinates. Naturality of the product comparison identifies the composite
with the direct comparison followed by the image of alpha; this is precisely the
horizontal Roos coherence equation. The scalarRoosTensorNormalization equations
identify these maps with scalarLimitTensor, including the canonical derived
composition units. Localize the equality and cancel the normalization isomorphisms.
No evaluation of maps in the derived diagram category is used. -/
theorem scalarLimitTensor_composition
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (j : F →ₐ[ℚ_[l]] L) (k : E →ₐ[ℚ_[l]] L) (W : Scheme.{u})
    (α : pbcExtend (constantMap l E F i W) ⋙ pbcExtend (constantMap l F L j W) ≅
      pbcExtend (constantMap l E L k W))
    (K : Derived (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
    (letI := (baseTensor_exact l E F i W).1
     letI := (baseTensor_exact l E F i W).2
     letI := (baseTensor_exact l F L j W).1
     letI := (baseTensor_exact l F L j W).2
     letI := (baseTensor_exact l E L k W).1
     letI := (baseTensor_exact l E L k W).2
     ((Functor.mapDerivedCategoryCompIso
       (pbcExtend (constantMap l E F i W)) (pbcExtend (constantMap l F L j W))).symm ≪≫
       Functor.mapDerivedCategoryNatIso α).hom.app ((scalarLimit l E W).obj K)) ≫
        (scalarLimitTensor l E L k W).hom.app K =
      (baseTensor l F L j W).map ((scalarLimitTensor l E F i W).hom.app K) ≫
        (scalarLimitTensor l F L j W).hom.app ((T l E F i W).obj K) ≫
        (scalarLimit l L W).map
          ((letI := (tensor_exact l E F i W).1
            letI := (tensor_exact l E F i W).2
            letI := (tensor_exact l F L j W).1
            letI := (tensor_exact l F L j W).2
            letI := (tensor_exact l E L k W).1
            letI := (tensor_exact l E L k W).2
            (Functor.mapDerivedCategoryCompIso (tensor l E F i W)
              (tensor l F L j W)).symm ≪≫
              Functor.mapDerivedCategoryNatIso
                (show tensor l E F i W ⋙ tensor l F L j W ≅ tensor l E L k W from
                  (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso α)).hom.app K) := by
  have := (baseTensor_exact l E F i W).1
  have := (baseTensor_exact l E F i W).2
  have := (baseTensor_exact l F L j W).1
  have := (baseTensor_exact l F L j W).2
  have := (baseTensor_exact l E L k W).1
  have := (baseTensor_exact l E L k W).2
  have := (tensor_exact l E F i W).1
  have := (tensor_exact l E F i W).2
  have := (tensor_exact l F L j W).1
  have := (tensor_exact l F L j W).2
  have := (tensor_exact l E L k W).1
  have := (tensor_exact l E L k W).2
  have := (scalarLimitTensor_exact l E F i W).2.2.1
  have := (scalarLimitTensor_exact l F L j W).2.2.1
  have := (scalarLimitTensor_exact l E L k W).2.2.1
  have := (scalarLimitTensor_exact l E F i W).2.2.2
  have := (scalarLimitTensor_exact l F L j W).2.2.2
  have := (scalarLimitTensor_exact l E L k W).2.2.2
  let H₀ : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W := lim
  let H₁ : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W := lim
  let H₂ : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W ⥤
      Modules (ULift.{u + 1} (Padic.coefficientExtensionIntegers l L)) W := lim
  let y₁ := pbcExtend (constantMap l E F i W)
  let y₂ := pbcExtend (constantMap l F L j W)
  let y₃ := pbcExtend (constantMap l E L k W)
  let x₁ := tensor l E F i W
  let x₂ := tensor l F L j W
  let x₃ := tensor l E L k W
  let c₁ : H₀ ⋙ y₁ ≅ x₁ ⋙ H₁ := preservesLimitNatIso (J := ℕᵒᵖ) y₁
  let c₂ : H₁ ⋙ y₂ ≅ x₂ ⋙ H₂ := preservesLimitNatIso (J := ℕᵒᵖ) y₂
  let c₃ : H₀ ⋙ y₃ ≅ x₃ ⋙ H₂ := preservesLimitNatIso (J := ℕᵒᵖ) y₃
  let a : x₁ ⋙ x₂ ≅ x₃ := (Functor.whiskeringRight ℕᵒᵖ _ _).mapIso α
  have hc (M : Towers (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W) :
      α.hom.app (H₀.obj M) ≫ c₃.hom.app M =
        y₂.map (c₁.hom.app M) ≫ c₂.hom.app (x₁.obj M) ≫ H₂.map (a.hom.app M) := by
    apply limit.hom_ext
    intro n
    change α.hom.app (limit M) ≫ (preservesLimitIso y₃ M).hom ≫ limit.π _ n =
      y₂.map (preservesLimitIso y₁ M).hom ≫
        (preservesLimitIso y₂ (M ⋙ y₁)).hom ≫
          limMap (Functor.whiskerLeft M α.hom) ≫ limit.π _ n
    simp only [preservesLimitIso_hom_π, limMap_π,
      Functor.whiskerLeft_app, preservesLimitIso_hom_π_assoc]
    rw [← y₂.map_comp_assoc, preservesLimitIso_hom_π]
    exact (α.hom.naturality (limit.π M n)).symm
  have hn₁ := tensorSquare_normalized H₀ H₁ x₁ y₁ c₁
  have hn₂ := tensorSquare_normalized H₁ H₂ x₂ y₂ c₂
  have hn₃ := tensorSquare_normalized H₀ H₂ x₃ y₃ c₃
  have h := normalized_horizontal H₀ H₁ H₂ x₁ x₂ x₃ y₁ y₂ y₃ c₁ c₂ c₃
    _ _ _ hn₁ hn₂ hn₃ a α hc K
  simpa only [H₀, H₁, H₂, x₁, x₂, x₃, y₁, y₂, y₃, c₁, c₂, c₃, a,
    scalarLimitTensor, scalarLimit, baseTensor, T] using h

end WeilConjectures.PurStrictScalar
