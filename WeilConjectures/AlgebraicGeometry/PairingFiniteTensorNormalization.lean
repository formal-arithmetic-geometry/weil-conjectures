/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PairingFiniteRealization

/-! # Normalized finite tensor coordinates for the pairing

Source: main-20261015, sec-poincare-duality/sk-def-pairing-data/_section.md,
first displayed composite; Stacks Tags 00YV, 0GMW and 06YN.
(blueprint: def-pod-pairing-tensor-normalization).
The comparison is determined on every K-flat representative by its value on
local pure tensors, including the signed total differential.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
open scoped TensorProduct
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- The ordinary signed-total comparison type.
Source: Stacks 06YN (blueprint: def-pod-pairing-tensor-normalization). -/
def PairingRealizationChainComparison (P Q : pairingFixedComplex l E X m) :=
(pairingRealizationComplex l E X m).obj (P ⊗ Q) ≅
          (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X m)).obj
              ((pairingRealizationComplex l E X m).obj P,
                (pairingRealizationComplex l E X m).obj Q)

/-- Every homogeneous local pure tensor is sent to the same realized tensor.
Source: Stacks 0GMW and 06YN (blueprint: def-pod-pairing-tensor-normalization). -/
def PairingRealizationChainNormalized (P Q : pairingFixedComplex l E X m)
    (c : PairingRealizationChainComparison l E X m P Q) : Prop :=
∀ (p q k : ℤ) (h : p + q = k) (U : X.ProEtᵒᵖ)
          (x : (P.X p).obj.obj U) (y : (Q.X q).obj.obj U),
          (c.hom.f k).val.app U
            (pairingRealizationSection l E X m ((P ⊗ Q).X k) U
              (pairingFixedTensorGenerator l E X m P Q p q k h U x y)) =
          coefficientTensorGenerator.{u, u + 1, u} (ProEt.topology X)
            (integralCoefficientCommRingSheaf l E X m)
            ((pairingRealizationComplex l E X m).obj P)
            ((pairingRealizationComplex l E X m).obj Q) p q k h U
            (pairingRealizationSection l E X m (P.X p) U x)
            (pairingRealizationSection l E X m (Q.X q) U y)

end WeilConjectures

namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- The two derived tensor bifunctors to be identified.
Source: Stacks 06YU (blueprint: def-pod-pairing-tensor-normalization). -/
def PairingRealizationTensorComparison :=
      (Functor.uncurry.obj (AlgebraicGeometry.ProEtale.derivedTensor
        (ModuleCat.{u + 1} (ULift.{u + 1, u}
          (Padic.coefficientExtensionRing l E (m + 1)))) X)) ⋙
          (pairingDerivedRealization l E X m).functor ≅
      ((pairingDerivedRealization l E X m).functor.prod
        (pairingDerivedRealization l E X m).functor) ⋙
        finiteIntrinsicDerivedTensor l E X m

/-- The full K-flat square through both localization comparisons.
Source: Stacks 06YU (blueprint: def-pod-pairing-tensor-normalization). -/
def PairingRealizationTensorNormalized
    (e : PairingRealizationTensorComparison l E X m) : Prop :=
      ∀ (P Q : pairingFixedComplex l E X m)
        (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X m)
          ((pairingRealizationComplex l E X m).obj P))
        (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X m)
          ((pairingRealizationComplex l E X m).obj Q)),
      ∃ c : PairingRealizationChainComparison l E X m P Q,
        PairingRealizationChainNormalized l E X m P Q c ∧
        HEq
          (e.hom.app (DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj P,
              DerivedCategory.Q.{u + 1, u + 1, u + 2}.obj Q) ≫
            (finiteIntrinsicDerivedTensor l E X m).map (Prod.mkHom
              ((Functor.mapDerivedCategoryFactors.{u + 1, u + 2}
                (pairingRealizationEquivalence l E X m).functor).hom.app P)
              ((Functor.mapDerivedCategoryFactors.{u + 1, u + 2}
                (pairingRealizationEquivalence l E X m).functor).hom.app Q)))
          ((pairingDerivedRealization l E X m).functor.map
              (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
            (Functor.mapDerivedCategoryFactors.{u + 1, u + 2}
              (pairingRealizationEquivalence l E X m).functor).hom.app
              (P ⊗ Q) ≫ DerivedCategory.Q.map c.hom ≫
            (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
              (integralCoefficientCommRingSheaf l E X m)
              (finiteIntrinsicClosed l E X m) (finiteIntrinsicTensorModels l E X m)
              ((pairingRealizationComplex l E X m).obj P)
              ((pairingRealizationComplex l E X m).obj Q) hP hQ).hom)

end WeilConjectures
