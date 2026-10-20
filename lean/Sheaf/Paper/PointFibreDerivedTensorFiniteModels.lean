/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.Paper.PointFibreDerivedTensorBasic

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # Canonical point tensor comparison interfaces

Source: Stacks 07A4 and the recorded coefficient constructions.
(blueprint: def-sf-point-fibre-tensor-finite-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v c e d hc he hd w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Opposite
open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

/-- Canonical normalization of the finite comparison on every K-flat presentation.
The chain comparison sends the actual sheaf tensor generator to the tensor of its
sections. The final equation fixes the derived comparison, through the recorded
`finiteIntrinsicTensorModels` and the native derived-localization tensor map.
Source: Stacks 07A4, proof (blueprint: def-sf-point-fibre-tensor-finite-models). -/
def PointFiniteTensorCanonical
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ)
    (S : PointFiniteTensorData D l E n) : Prop :=
  ∀ (P Q : CochainComplex (normalizedDVRModules l E (Spec (.of D.k)) n) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (Scheme.ProEt (Spec (.of D.k))) inferInstance (essentiallySmallSelf.{0} _)
      (Scheme.ProEt.topology (Spec (.of D.k)))
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (Scheme.ProEt (Spec (.of D.k))) inferInstance (essentiallySmallSelf.{0} _)
      (Scheme.ProEt.topology (Spec (.of D.k)))
      (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n) Q)
    (hcP : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Spec (.of D.k)) (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P))
    (hcQ : finiteTorConstructible l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
      (Spec (.of D.k)) (DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj Q)),
    ∃ e : (pointFiniteComplexSections D l E n).obj
        ((coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology (Spec (.of D.k)))
          (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)).obj (P, Q)) ≅
      (pointFiniteComplexSections D l E n).obj P ⊗
        (pointFiniteComplexSections D l E n).obj Q,
      (∀ (p q k : ℤ) (h : p + q = k)
        (x : (P.X p).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))))
        (y : (Q.X q).val.obj (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (e.hom.f k) (coefficientTensorGenerator.{u, u + 1, u}
          (Scheme.ProEt.topology (Spec (.of D.k)))
          (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)
          P Q p q k h (op (Scheme.ProEt.mk (𝟙 (Spec (.of D.k))))) x y) =
        (HomologicalComplex.ιTensorObj
          ((pointFiniteComplexSections D l E n).obj P)
          ((pointFiniteComplexSections D l E n).obj Q) p q k h)
            (x ⊗ₜ[ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1))] y)) ∧
      HEq
      ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
        (n + 1))).mapDerivedCategory.{u + 2, u + 1}.map
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 2}
            (Scheme.ProEt.topology (Spec (.of D.k)))
            (integralCoefficientCommRingSheaf l E (Spec (.of D.k)) n)
            (finiteIntrinsicClosed l E (Spec (.of D.k)) n)
            (finiteIntrinsicTensorModels l E (Spec (.of D.k)) n) P Q hP hQ).hom ≫
        (pointFiniteTensorComparison D l E n S ⟨DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj P, hcP⟩
          ⟨DerivedCategory.Q.{u + 2, u + 1, u + 2}.obj Q, hcQ⟩).hom ≫
        (MonoidalCategory.tensor (DerivedCategory (ModuleCat.{u + 1}
          (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E (n + 1)))))).map
          (Prod.mkHom
            ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
              (n + 1))).mapDerivedCategoryFactors.{u + 2, u + 1}.hom.app P)
            ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
              (n + 1))).mapDerivedCategoryFactors.{u + 2, u + 1}.hom.app Q)) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((pointFiniteComplexSections D l E n).obj P)
          ((pointFiniteComplexSections D l E n).obj Q))
      ((pointFiniteSections D.k (Padic.coefficientExtensionRing l E
        (n + 1))).mapDerivedCategoryFactors.{u + 2, u + 1}.hom.app _ ≫ DerivedCategory.Q.map e.hom)

end WeilConjectures
