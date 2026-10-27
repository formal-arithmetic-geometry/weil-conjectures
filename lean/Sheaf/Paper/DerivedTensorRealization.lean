/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B4
-/
module

public import Sheaf.Paper.LisseTensorPullbackRealizationData

/-! # The derived tensor calculation before specialization to the lisse heart

Source: Bhatt--Scholze Remark 6.8.15; Stacks 07A4.
(blueprint: lem-real-derived-tensor-calculation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme MonoidalCategory
open scoped TensorProduct MonoidalCategory
namespace WeilConjectures.LisseRealization
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Derived tensor, its good-model calculation and scalar unit, before any heart claim.
Source: BS Remark 6.8.15; Stacks 07A4
(blueprint: lem-real-derived-tensor-calculation). -/
structure DerivedTensorRealization (X : Base D l hl) (a : At D l hl E X) where
  comparison : constructibleIntegralTensor l E X.scheme ⋙
      (sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a) ≅
    (((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a)).prod
      ((sfIntegralConstructible l E X.scheme).ι ⋙ pbcDerivedExtend (scalar D l hl E a))) ⋙
        realizationOrdinaryTensor D l hl E X
  models : ∀ (K L : sfIntegralConstructibleCategory l E X.scheme)
    (P Q : (integralOperationsGoodComplex l E X.scheme).FullSubcategory)
    (eP : DerivedCategory.Q.obj P.obj ≅ K.obj)
    (eQ : DerivedCategory.Q.obj Q.obj ≅ L.obj),
    ∃ m : RealizationTensorCalculation D l hl E a K L P Q eP eQ,
      HEq (comparison.hom.app (K, L)) (m.arrow D l hl E)
  raw : tensor D l hl E X ⋙ a.J ≅ (a.J.prod a.J) ⋙ realizationOrdinaryTensor D l hl E X
  integral : ∀ K L : sfIntegralConstructibleCategory l E X.scheme,
    HEq (raw.hom.app ((sfRationalConstructibleLocalization l E X.scheme).obj K,
      (sfRationalConstructibleLocalization l E X.scheme).obj L))
      (a.integral.hom.app ((constructibleIntegralTensor l E X.scheme).obj (K, L)) ≫
        comparison.hom.app (K, L) ≫
        (realizationOrdinaryTensor D l hl E X).map
          (Prod.mkHom (a.integral.inv.app K) (a.integral.inv.app L)))
  unit : (pbcExtend (scalar D l hl E a)).obj
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme)) ≅
    SheafOfModules.unit ((adicLisseForget X.scheme).obj (rationalCoefficientSheaf l X.scheme E))
  unit_sections : ∀ (U : X.scheme.ProEtᵒᵖ)
    (c : (rationalCoefficientSheaf l X.scheme E).obj.obj U)
    (b : (completedIntegralCommRingSheafUnrestricted l E X.scheme).obj.obj U),
    unit.hom.val.app U (pbcTensorSection (scalar D l hl E a)
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))
      U c b) = c * ((scalar D l hl E a).hom.app U b)


  derived_unit : (pbcDerivedExtend (scalar D l hl E a)).obj
      ((DerivedCategory.singleFunctor _ 0).obj
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≅
    (DerivedCategory.singleFunctor _ 0).obj
      (SheafOfModules.unit ((adicLisseForget X.scheme).obj
        (rationalCoefficientSheaf l X.scheme E)))
  derived_unit_normalized : derived_unit.hom =
    (pbcDerivedExtend (scalar D l hl E a)).map
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app _) ≫
      pbcComplexCounit (scalar D l hl E a)
        ((CochainComplex.singleFunctor _ 0).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex
          (pbcExtend (scalar D l hl E a)) (.up ℤ) 0).hom.app _) ≫
      (DerivedCategory.singleFunctorIsoCompQ (Modules D l hl E X) 0).inv.app
        ((pbcExtend (scalar D l hl E a)).obj
          (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E X.scheme))) ≫
      (DerivedCategory.singleFunctor _ 0).map unit.hom

/-- The derived comparison on all constructible pairs, with its specified models and unit.
Source: Bhatt--Scholze Remark 6.8.15; Stacks 07A4
(blueprint: lem-real-derived-tensor-calculation).

Proof: a finite-type scheme over the field D.k is noetherian and qcqs, and l is
invertible in every residue field. Apply constructibleTensorCompletion. Its natural
map tau is invertible on constructible pairs, so restrict its inverse to that full
subcategory. Compose its image under scalar extension with the ordinary derived
scalar tensor constraint. On good representatives the completion theorem identifies
tau with Q(chi), including both its quotient coordinates and its zero shifted
coordinate. The ordinary scalar constraint is the balanced map
c tensor (x tensor y) to (1 tensor x) tensor (c tensor y); its inverse multiplies
the two scalars. The scalar degree is zero, so these maps commute with the signed
total differential. Scalar extension preserves flat-term K-flat representatives,
and its universal counit gives precisely the left and right comparisons in models.
Conjugate the integral comparison by a.integral. Extend its naturality from integral
arrows to localized arrows: a fraction multiplies both sides by the same scalar,
and additivity treats sums. Objects of raw localization are unchanged, so this
produces raw with the stated integral equation. For the unit use multiplication
c tensor b to c scalar(b), whose inverse inserts one. The single B[0] is flat-term
K-flat; its scalar counit and the termwise single comparison give derived_unit,
with exactly the displayed composite. This argument permits torsion representatives,
empty schemes and rank zero; it makes no claim about the lisse heart. -/
theorem derived_tensor_realization (X : Base D l hl) (a : At D l hl E X) :
    Nonempty (DerivedTensorRealization D l hl E X a) := by sorry

end WeilConjectures.LisseRealization
