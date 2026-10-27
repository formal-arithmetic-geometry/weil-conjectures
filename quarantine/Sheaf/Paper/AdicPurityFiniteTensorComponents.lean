/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityRootComparisons
/-! # Components of the intrinsic finite tensor comparison
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: lem-pur-adic-finite-tensor-components).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) (T : Scheme.{u})
section TwistReduction
variable [hInvert : ∀ x : T, Invertible (l : T.residueField x)]
include hInvert

/-- The intrinsic finite tensor comparison on one module, normalized on all
scalar-unit pure tensors.
Source: def-coefficient-twists-detailed, finite tensor realization; Stacks 00YV and 03EK.
(blueprint: lem-pur-adic-finite-tensor-components).
Proof: restrict the given intrinsic line to constant scalars. The scalar-unit
map identifies its associated intrinsic module with the original line. Tensor
the realization units on sectionwise fixed-coefficient tensors and extend through
module sheafification. Locally every scalar of the constant ring sheaf is a
constant scalar, so the fixed-scalar and intrinsic balanced relations agree.
The resulting map and its inverse both fix pure tensors. They descend through
sheafification to the desired isomorphism and give the displayed equation.
The argument uses only the two universal properties and applies also to zero
rings, zero modules and empty test objects. -/
theorem adicPurityFiniteTensor_component (d : ℕ)
    (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) :
    ∃ e : (SheafOfModules.siteSheafTensorRight
        (A := integralCoefficientCommRingSheaf l E T n)
        (finiteCoefficientTwist l E T n (d : ℤ))).obj
          ((sfIntrinsicModuleEquivalence T
            (Padic.coefficientExtensionRing l E (n + 1))).functor.obj M) ≅
      (sfIntrinsicModuleEquivalence T
        (Padic.coefficientExtensionRing l E (n + 1))).functor.obj
          (M ⊗ finiteTateProSheaf l E n T d),
      ∀ (W : T.ProEtᵒᵖ) (x : M.obj.obj W)
        (y : (finiteCoefficientTwist l E T n (d : ℤ)).val.obj W),
        e.hom.val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W
            (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W x) y) =
        sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
          (M ⊗ finiteTateProSheaf l E n T d) W
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M
              (finiteTateProSheaf l E n T d)).app W (x ⊗ₜ[finiteTateCoefficient l E n] y)) := by
  sorry

end TwistReduction
end WeilConjectures
