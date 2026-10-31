/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorHom
/-! # Coefficient-unit coordinates for the normalized trace
Source: main-20261015, sec-poincare-duality/sk-def-pairing-data/_section.md,
second displayed composite; Stacks Tags 06YN and 07A4.
(blueprint: def-pod-pairing-coefficient-unit).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (m : ℕ)

/-- The finite coefficient object in degree zero.
Source: Stacks 06YN (blueprint: def-pod-pairing-coefficient-unit). -/
def pairingFiniteCoefficientUnit :=
  DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
    (SheafOfModules.unit (integralCoefficientSheaf l E X m)))

/-- Scalar multiplication on every K-flat total representative fixes the unit
comparison, including its scalar normalization.
Source: Stacks 06YN (blueprint: def-pod-pairing-coefficient-unit). -/
def PairingFiniteUnitNormalized
    (e : (finiteIntrinsicClosed l E X m).monoidal.tensorUnit ≅
      pairingFiniteCoefficientUnit l E X m) : Prop :=
  ∀ (P : CochainComplex (normalizedDVRModules l E X m) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
      (ProEt.topology X) (integralCoefficientCommRingSheaf l E X m) P),
    ∃ (hU : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        X.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology X) (integralCoefficientCommRingSheaf l E X m)
        ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
          (SheafOfModules.unit (integralCoefficientSheaf l E X m))))
      (ρ : (coefficientTotalTensor.{u, u + 1, u} (ProEt.topology X)
          (integralCoefficientCommRingSheaf l E X m)).obj
            (P, (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
              (SheafOfModules.unit (integralCoefficientSheaf l E X m))) ⟶ P),
      (∀ (p : ℤ) (U : X.ProEtᵒᵖ) (x : (P.X p).val.obj U)
        (a : (integralCoefficientCommRingSheaf l E X m).obj.obj U),
        (ρ.f p).val.app U (coefficientTensorGenerator.{u, u + 1, u}
          (ProEt.topology X) (integralCoefficientCommRingSheaf l E X m) P
          ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).obj
            (SheafOfModules.unit (integralCoefficientSheaf l E X m)))
          p 0 p (Int.add_zero p) U x a) = a • x) ∧
      (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology X)
        (integralCoefficientCommRingSheaf l E X m) (finiteIntrinsicClosed l E X m)
        (finiteIntrinsicTensorModels l E X m) P _ hP hU).hom ≫
        (finiteIntrinsicDerivedTensor l E X m).map (Prod.mkHom (𝟙 _) e.inv) ≫
        ((finiteIntrinsicClosed l E X m).monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom =
          DerivedCategory.Q.map ρ

/-- The coefficient unit has a unique scalar-multiplication-normalized comparison.
Source: Stacks 06YN, 06YU and 07A4 (blueprint: def-pod-pairing-coefficient-unit).
Proof: tensoring a K-flat complex with the degree-zero coefficient computes
that complex by scalar multiplication. Descend this natural isomorphism through
the recorded tensor model. The monoidal unit universal property identifies its
coefficient object with the recorded unit. The right-unitor equation determines
the comparison; every derived object has a K-flat resolution, hence this
normalization determines the comparison uniquely. -/
theorem pairingFiniteUnit_existsUnique :
    ∃! e : (finiteIntrinsicClosed l E X m).monoidal.tensorUnit ≅
      pairingFiniteCoefficientUnit l E X m, PairingFiniteUnitNormalized l E X m e := by
  sorry

/-- The unique normalized finite coefficient-unit comparison.
Source: normalized trace target (blueprint: def-pod-pairing-coefficient-unit). -/
def pairingFiniteUnit := (pairingFiniteUnit_existsUnique l E X m).exists.choose

end WeilConjectures
