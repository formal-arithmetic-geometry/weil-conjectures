/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PointTateFiberComparisonData
public import Sheaf.Paper.IsomorphismComparisonScalarExtension
import Sheaf.Paper.IntegralTwistBaseChange

/-! # Constructed comparison maps for point Tate sections

Source: the coefficient comparison lemma, steps 3--5.
(blueprint: def-pur-point-tate-canonical-comparisons).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] AlgebraicGeometry.Scheme.residueLisseAlgebraHasDerivedCategory
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings TensorProduct
namespace WeilConjectures.PointTateFiber

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]

/-- Pass from the completed ordinary model to the original normalized signed line map.
Source: coefficient comparison lemma, step 3
(blueprint: def-pur-point-tate-canonical-comparisons). -/
def canonicalSheaf (hl : l ≠ D.p) : SheafComparisons D l :=
  fun F _ _ _ L _ _ _ ι m ↦
    letI := frobeniusPointPrimeInvertible D l hl
    ((isomorphismScalarSheafModel l F L ι (Spec (.of D.k))).app
      (integralTwistLine l F (Spec (.of D.k)) m)).symm ≪≫
      twistLineScalarIso l F (Spec (.of D.k)) L ι m

/-- Evaluate the actual sections-tensor comparison followed by the signed line map.
Source: coefficient comparison lemma, step 4
(blueprint: def-pur-point-tate-canonical-comparisons). -/
def canonicalIntegral (hl : l ≠ D.p) : IntegralComparisons D l :=
  fun F _ _ _ L _ _ _ ι m ↦
    (pointSectionsTensor D.k l F L ι).app (integralTwistLine l F (Spec (.of D.k)) m) ≪≫
      (pointCompletedSections D.k l L).mapIso (canonicalSheaf D l hl F L ι m)

/-- Rationalize the integral map using the fixed localization-tensor associator.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
def canonicalRational (hl : l ≠ D.p) : RationalComparisons D l :=
  fun F _ _ _ L _ _ _ ι m ↦
    ((pointTensorRationalization_existsUnique l F L ι).exists.choose.app
      (integral D l F m)).symm ≪≫
      (pointModuleRationalization l L).mapIso (canonicalIntegral D l hl F L ι m)

/-- The constructed sheaf isomorphism has the published pure-tensor normalization.
Source: coefficient comparison lemma, step 3
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalSheaf_tensor (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L) (m : ℤ) (U : (Spec (.of D.k)).ProEtᵒᵖ)
    (b : (completedIntegralCommRingSheafUnrestricted l L (Spec (.of D.k))).obj.obj U)
    (x : (integralTwistLine l F (Spec (.of D.k)) m).val.obj U) :
    (canonicalSheaf D l hl F L ι m).hom.val.app U
        (completedScalarTensorSection l F L ι (Spec (.of D.k)) _ U b x) =
      b • (@id ((integralTwistLine l L (Spec (.of D.k)) m).val.obj U)
        ((scalarMap D l F hl L ι m).val.app U x)) := by
  let := frobeniusPointPrimeInvertible D l hl
  have h := (isomorphismScalarSheafModel_existsUnique l F L ι
    (Spec (.of D.k))).exists.choose_spec
      (integralTwistLine l F (Spec (.of D.k)) m) U b x
  have hi := congrArg (fun f ↦ f.val.app U
    (integralOrdinaryTensorSection l F L ι (Spec (.of D.k)) _ U b x))
      ((isomorphismScalarSheafModel l F L ι (Spec (.of D.k))).app
        (integralTwistLine l F (Spec (.of D.k)) m)).hom_inv_id
  have he : ((isomorphismScalarSheafModel l F L ι (Spec (.of D.k))).inv.app
      (integralTwistLine l F (Spec (.of D.k)) m)).val.app U
        (completedScalarTensorSection l F L ι (Spec (.of D.k)) _ U b x) =
      integralOrdinaryTensorSection l F L ι (Spec (.of D.k)) _ U b x :=
    (congrArg (fun y ↦ ((isomorphismScalarSheafModel l F L ι
      (Spec (.of D.k))).inv.app (integralTwistLine l F (Spec (.of D.k)) m)).val.app U y)
      h).symm.trans hi
  change (twistLineScalarIso l F (Spec (.of D.k)) L ι m).hom.val.app U _ = _
  exact (congrArg ((twistLineScalarIso l F (Spec (.of D.k)) L ι m).hom.val.app U)
    he).trans ((integral_twist_base_change l F L ι (Spec (.of D.k))).2.1 m U b x)

/-- The constructed integral isomorphism on arbitrary section tensors.
Source: coefficient comparison lemma, steps 3--4
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalIntegral_tensor (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L) (m : ℤ)
    (b : Padic.coefficientExtensionIntegers l L) (x : integral D l F m) :
    (canonicalIntegral D l hl F L ι m).hom
        (b ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          integralScalarIntegerInclusion l F L ι] x) =
      b • (@id (integral D l L m) ((scalarMap D l F hl L ι m).val.app (finalObject D) x)) := by
  change (canonicalSheaf D l hl F L ι m).hom.val.app (finalObject D)
    ((pointSectionsTensor D.k l F L ι).hom.app _ _) = _
  have h := (pointSectionsTensor_existsUnique D.k l F L ι).exists.choose_spec
    (integralTwistLine l F (Spec (.of D.k)) m) b x
  exact (congrArg ((canonicalSheaf D l hl F L ι m).hom.val.app (finalObject D))
    h).trans (canonicalSheaf_tensor D l hl F L ι m (finalObject D)
      (pointCompletedConstant D.k l L b) x)

/-- Rationalization of the constructed integral map is exactly the specified composite.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalRational_compatibility (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L) (m : ℤ) :
    (pointModuleRationalization l L).map (canonicalIntegral D l hl F L ι m).hom =
      ((pointTensorRationalization_existsUnique l F L ι).exists.choose).hom.app
        (integral D l F m) ≫ (canonicalRational D l hl F L ι m).hom := by
  change _ =
    ((pointTensorRationalization_existsUnique l F L ι).exists.choose.app
      (integral D l F m)).hom ≫
    ((pointTensorRationalization_existsUnique l F L ι).exists.choose.app
      (integral D l F m)).inv ≫ _
  rw [Iso.hom_inv_id_assoc]
  rfl

/-- The rational map on tensors of an arbitrary integral section.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalRational_tensor (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L) (m : ℤ) (b : L) (x : integral D l F m) :
    (canonicalRational D l hl F L ι m).hom
        (b ⊗ₜ[F, ι.toRingHom] ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] x)) =
      b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
        algebraMap (Padic.coefficientExtensionIntegers l L) L]
        (@id (integral D l L m) ((scalarMap D l F hl L ι m).val.app (finalObject D) x)) := by
  have h := (pointTensorRationalization_existsUnique l F L ι).exists.choose_spec
    (integral D l F m) 1 b x
  have hh := congrArg (fun f ↦ f
    (b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
      algebraMap (Padic.coefficientExtensionIntegers l L) L]
      ((1 : Padic.coefficientExtensionIntegers l L)
        ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          integralScalarIntegerInclusion l F L ι] x)))
    (canonicalRational_compatibility D l hl F L ι m)
  simp only [OneMemClass.coe_one, mul_one] at h
  change (pointModuleRationalization l L).map (canonicalIntegral D l hl F L ι m).hom _ =
    (canonicalRational D l hl F L ι m).hom _ at hh
  have ha := canonicalIntegral_tensor D l hl F L ι m 1 x
  rw [one_smul] at ha
  calc
    _ = (canonicalRational D l hl F L ι m).hom
        (((pointTensorRationalization_existsUnique l F L ι).exists.choose).hom.app
          (integral D l F m) _) := congrArg _ h.symm
    _ = (pointModuleRationalization l L).map
        (canonicalIntegral D l hl F L ι m).hom _ := hh.symm
    _ = b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          algebraMap (Padic.coefficientExtensionIntegers l L) L]
          ((canonicalIntegral D l hl F L ι m).hom
            ((1 : Padic.coefficientExtensionIntegers l L)
              ⊗ₜ[Padic.coefficientExtensionIntegers l F,
                integralScalarIntegerInclusion l F L ι] x)) :=
      ModuleCat.ExtendScalars.map_tmul _ _ b _
    _ = _ := congrArg (fun y ↦ b ⊗ₜ[Padic.coefficientExtensionIntegers l L,
      algebraMap (Padic.coefficientExtensionIntegers l L) L] y) ha

/-- The integral comparison for the identity embedding is multiplication.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalIntegral_identity (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (m : ℤ) :
    (canonicalIntegral D l hl F F (AlgHom.id (Padic l) F) m).hom =
      ((pointIntegralModuleUnit_existsUnique l F).exists.choose).hom.app (integral D l F m) := by
  let := frobeniusPointPrimeInvertible D l hl
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  have h₁ := canonicalIntegral_tensor D l hl F F (AlgHom.id (Padic l) F) m 1 x
  have h₂ := twistScalarMaps_identity l F (Spec (.of D.k)) m (finalObject D) x
  have h₃ := (pointIntegralModuleUnit_existsUnique l F).exists.choose_spec
    (integral D l F m) 1 x
  simp only [one_smul] at h₁ h₃
  exact h₁.trans (h₂.trans h₃.symm)

/-- The integral comparison respects the specified tensor associator.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalIntegral_tower (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L)
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (κ : L →ₐ[Padic l] M) (m : ℤ) :
    (pointIntegralModuleTensor l L M κ).map (canonicalIntegral D l hl F L ι m).hom ≫
        (canonicalIntegral D l hl L M κ m).hom =
      ((pointIntegralModuleAssoc_existsUnique l F L ι M κ).exists.choose).hom.app
        (integral D l F m) ≫ (canonicalIntegral D l hl F M (κ.comp ι) m).hom := by
  let := frobeniusPointPrimeInvertible D l hl
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l L M κ)).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (integralScalarIntegerInclusion l F L ι)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (canonicalIntegral D l hl L M κ m).hom
      ((pointIntegralModuleTensor l L M κ).map
        (canonicalIntegral D l hl F L ι m).hom
        ((1 : Padic.coefficientExtensionIntegers l M)
          ⊗ₜ[Padic.coefficientExtensionIntegers l L,
            integralScalarIntegerInclusion l L M κ]
          ((1 : Padic.coefficientExtensionIntegers l L)
            ⊗ₜ[Padic.coefficientExtensionIntegers l F,
              integralScalarIntegerInclusion l F L ι] x))) =
    (canonicalIntegral D l hl F M (κ.comp ι) m).hom
      (((pointIntegralModuleAssoc_existsUnique l F L ι M κ).exists.choose).hom.app
        (integral D l F m) _)
  have h₁ := canonicalIntegral_tensor D l hl F L ι m 1 x
  have h₂ := canonicalIntegral_tensor D l hl L M κ m 1
    (@id (integral D l L m) ((scalarMap D l F hl L ι m).val.app (finalObject D) x))
  have h₃ := (pointIntegralModuleAssoc_existsUnique l F L ι M κ).exists.choose_spec
    (integral D l F m) 1 1 x
  have h₄ := canonicalIntegral_tensor D l hl F M (κ.comp ι) m 1 x
  simp only [one_smul] at h₁ h₂ h₄
  simp only [map_one, one_mul] at h₃
  rw [ModuleCat.ExtendScalars.map_tmul]
  exact ((congrArg (fun y ↦ (canonicalIntegral D l hl L M κ m).hom
      ((1 : Padic.coefficientExtensionIntegers l M)
        ⊗ₜ[Padic.coefficientExtensionIntegers l L,
          integralScalarIntegerInclusion l L M κ] y)) h₁).trans h₂).trans
    ((twistScalarMaps_composition l F (Spec (.of D.k)) L ι M κ m
      (finalObject D) x).symm.trans
      (h₄.symm.trans (congrArg (canonicalIntegral D l hl F M (κ.comp ι) m).hom h₃.symm)))

/-- The rational identity comparison is the canonical multiplication map.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalRational_identity (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (m : ℤ) :
    (canonicalRational D l hl F F (AlgHom.id (Padic l) F) m).hom =
      (ModuleCat.extendScalarsId.{u, u + 1} F).hom.app (rational D l F m) := by
  let := frobeniusPointPrimeInvertible D l hl
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} (RingHom.id F)).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l F) F)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (canonicalRational D l hl F F (AlgHom.id (Padic l) F) m).hom
      ((1 : F) ⊗ₜ[F, RingHom.id F]
        ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] x)) =
    (ModuleCat.extendScalarsId.{u, u + 1} F).hom.app (rational D l F m) _
  have h := canonicalRational_tensor D l hl F F (AlgHom.id (Padic l) F) m 1 x
  have he := twistScalarMaps_identity l F (Spec (.of D.k)) m (finalObject D) x
  exact h.trans ((congrArg (fun y : integral D l F m ↦
    (1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
    algebraMap (Padic.coefficientExtensionIntegers l F) F] y) he).trans
      (ModuleCat.extendScalarsId_hom_app_one_tmul.{u, u + 1} (rational D l F m)
        ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] x)).symm)

/-- The rational comparison respects the ordinary field tensor associator.
Source: coefficient comparison lemma, step 5
(blueprint: def-pur-point-tate-canonical-comparisons). -/
theorem canonicalRational_tower (hl : l ≠ D.p)
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : F →ₐ[Padic l] L)
    (M : Type u) [Field M] [Algebra (Padic l) M] [FiniteDimensional (Padic l) M]
    (κ : L →ₐ[Padic l] M) (m : ℤ) :
    (ModuleCat.extendScalars κ.toRingHom).map (canonicalRational D l hl F L ι m).hom ≫
        (canonicalRational D l hl L M κ m).hom =
      (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
        (rational D l F m) ≫ (canonicalRational D l hl F M (κ.comp ι) m).hom := by
  let := frobeniusPointPrimeInvertible D l hl
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} κ.toRingHom).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u} ι.toRingHom).homEquiv _ _).injective
  apply ((ModuleCat.extendRestrictScalarsAdj.{u + 1, u, u}
    (algebraMap (Padic.coefficientExtensionIntegers l F) F)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (canonicalRational D l hl L M κ m).hom
      ((ModuleCat.extendScalars κ.toRingHom).map
        (canonicalRational D l hl F L ι m).hom
        ((1 : M) ⊗ₜ[L, κ.toRingHom] ((1 : L) ⊗ₜ[F, ι.toRingHom]
          ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
            algebraMap (Padic.coefficientExtensionIntegers l F) F] x)))) =
    (canonicalRational D l hl F M (κ.comp ι) m).hom
      ((ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
        (rational D l F m) _)
  have h₁ := canonicalRational_tensor D l hl F L ι m 1 x
  have h₂ := canonicalRational_tensor D l hl L M κ m 1
    (@id (integral D l L m) ((scalarMap D l F hl L ι m).val.app (finalObject D) x))
  have h₄ := canonicalRational_tensor D l hl F M (κ.comp ι) m 1 x
  have h₃ : (ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
      (rational D l F m)
      ((1 : M) ⊗ₜ[L, κ.toRingHom] ((1 : L) ⊗ₜ[F, ι.toRingHom]
        ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] x))) =
      (1 : M) ⊗ₜ[F, (κ.comp ι).toRingHom]
        ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
          algebraMap (Padic.coefficientExtensionIntegers l F) F] x) := by
    have h := ModuleCat.extendScalarsComp_hom_app_one_tmul.{u, u + 1} ι.toRingHom κ.toRingHom
      (rational D l F m)
      ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
        algebraMap (Padic.coefficientExtensionIntegers l F) F] x)
    exact (congrArg ((ModuleCat.extendScalarsComp.{u, u + 1} ι.toRingHom κ.toRingHom).inv.app
      (rational D l F m)) h).symm.trans
        (congrArg (fun f ↦ f
          ((1 : M) ⊗ₜ[F, (κ.comp ι).toRingHom]
            ((1 : F) ⊗ₜ[Padic.coefficientExtensionIntegers l F,
              algebraMap (Padic.coefficientExtensionIntegers l F) F] x)))
          ((ModuleCat.extendScalarsComp.{u, u + 1}
            ι.toRingHom κ.toRingHom).hom_inv_id_app (rational D l F m)))
  rw [ModuleCat.ExtendScalars.map_tmul]
  exact ((congrArg (fun y ↦ (canonicalRational D l hl L M κ m).hom
      ((1 : M) ⊗ₜ[L, κ.toRingHom] y)) h₁).trans h₂).trans
    ((congrArg (fun y : integral D l M m ↦ (1 : M) ⊗ₜ[Padic.coefficientExtensionIntegers l M,
      algebraMap (Padic.coefficientExtensionIntegers l M) M] y)
      (twistScalarMaps_composition l F (Spec (.of D.k)) L ι M κ m
        (finalObject D) x).symm).trans
      (h₄.symm.trans (congrArg (canonicalRational D l hl F M (κ.comp ι) m).hom h₃.symm)))

end WeilConjectures.PointTateFiber
