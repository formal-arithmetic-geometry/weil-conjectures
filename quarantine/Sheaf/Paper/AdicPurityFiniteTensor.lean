/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Sheaf.Paper.AdicPurityRootComparisons
/-! # Derived reduction of the root-normalized integral twist
Source: blueprint def-coefficient-twists-detailed, finite reduction clause.
(blueprint: def-pur-adic-finite-tensor-realization).
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

/-- The actual ordinary finite tensor-by-line functor.
Source: blueprint twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityFiniteSheafTwist (d : ℕ) :=
  SheafOfModules.siteSheafTensorRight
    (A := integralCoefficientCommRingSheaf l E T n)
    (finiteCoefficientTwist l E T n (d : ℤ))

/-- The ordinary twist/restriction comparison is uniquely specified on all balanced
local tensors, using the root-normalized quotient map already constructed.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: send x tensor y to x tensor c_d(y). The quotient-line equations make this
balanced over the completed coefficient sheaf. It commutes with restriction and
therefore sheafifies. On a cover trivializing the integral line it is the identity
on the finite module, so it is invertible. Local tensor generation proves uniqueness. -/
theorem adicPurityTwistRestriction_existsUnique (d : ℕ) :
    ∃! e : scalarReductionRestriction l E T n ⋙ integralSheafTwist l E T (d : ℤ) ≅
      adicPurityFiniteSheafTwist l E n T d ⋙ scalarReductionRestriction l E T n,
      ∀ (M : scalarReductionTarget l E T n) (W : T.ProEtᵒᵖ)
        (x : M.val.obj W) (y : (integralTwistLine l E T (d : ℤ)).val.obj W),
        (e.hom.app M).val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := completedIntegralCommRingSheafUnrestricted l E T) _ _ W x y) =
          SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W x
              ((adicPurityRootQuotients l E n T d).val.app W y) := by
  sorry

/-- The ordinary comparison, with its pure-tensor normalization retained.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityTwistRestriction (d : ℕ) :=
  (adicPurityTwistRestriction_existsUnique l E n T d).exists.choose

/-- Exactness of the finite tensor-by-line functor, inherited from its invertible line.
Source: blueprint coefficient twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: the finite twisting line is locally free of rank one, hence tensoring with it
is locally isomorphic to the identity. Addition, kernels and cokernels descend from
these local identifications. -/
theorem adicPurityFiniteSheafTwist_exact (d : ℕ) :
    (adicPurityFiniteSheafTwist l E n T d).Additive ∧
      PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d) ∧
      PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d) := by
  sorry
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_additive (d : ℕ) :
    (adicPurityFiniteSheafTwist l E n T d).Additive :=
  (adicPurityFiniteSheafTwist_exact l E n T d).1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_limits (d : ℕ) :
    PreservesFiniteLimits (adicPurityFiniteSheafTwist l E n T d) :=
  (adicPurityFiniteSheafTwist_exact l E n T d).2.1
/-- Instance induced by the preceding named construction or property.
Source: blueprint adic reconstruction, canonical coefficient comparisons
(blueprint: def-pur-adic-finite-tensor-realization). -/
instance adicPurityFiniteSheafTwist_colimits (d : ℕ) :
    PreservesFiniteColimits (adicPurityFiniteSheafTwist l E n T d) :=
  (adicPurityFiniteSheafTwist_exact l E n T d).2.2

/-- Intrinsic and fixed-coefficient tensor-by-line functors agree on every local pure
tensor. The scalar-unit sections specify the realization map uniquely.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: both tensor constructions sheafify the same balanced tensors. Send the scalar-unit
section of m tensor y to the scalar-unit section of m tensor y in the fixed tensor.This
 respects locally constant coefficients and restrictions. Such sections locally
generate, giving uniqueness and an inverse. -/
theorem adicPurityFiniteTensorRealization_existsUnique (d : ℕ) :
    ∃! e : (sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
        adicPurityFiniteSheafTwist l E n T d ≅
      tensorRight (finiteTateProSheaf l E n T d) ⋙
        (sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor,
      ∀ (M : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (finiteTateCoefficient l E n)))
        (W : T.ProEtᵒᵖ) (x : M.obj.obj W)
        (y : (finiteCoefficientTwist l E T n (d : ℤ)).val.obj W),
        (e.hom.app M).val.app W
          (SheafOfModules.siteSheafTensorTmul
            (A := integralCoefficientCommRingSheaf l E T n) _ _ W
            (sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1)) M W x) y) =
        sfIntrinsicRealizationUnit T (Padic.coefficientExtensionRing l E (n + 1))
          (M ⊗ finiteTateProSheaf l E n T d) W
          ((Functor.LaxMonoidal.μ (sheafToPresheaf (ProEt.topology T)
            (ModuleCat.{u + 1} (finiteTateCoefficient l E n))) M
              (finiteTateProSheaf l E n T d)).app W (x ⊗ₜ[finiteTateCoefficient l E n] y)) := by
  sorry

/-- The finite ordinary tensor realization with its scalar-unit normalization.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization). -/
def adicPurityFiniteTensorRealization (d : ℕ) :=
  (adicPurityFiniteTensorRealization_existsUnique l E n T d).exists.choose

/-- The ordinary intrinsic tensor realization preserves zero arrows.
Source: blueprint finite twists (blueprint: def-pur-adic-finite-tensor-realization).
Proof: realization is additive and tensoring with the finite line is additive. Their
composite therefore sends the zero linear map to the zero linear map, on every section. -/
theorem adicPurityFiniteTensorComposite_zero (d : ℕ) :
    ((sfIntrinsicModuleEquivalence T (Padic.coefficientExtensionRing l E (n + 1))).functor ⋙
      adicPurityFiniteSheafTwist l E n T d).PreservesZeroMorphisms := by
  sorry
attribute [instance] adicPurityFiniteTensorComposite_zero

end TwistReduction
end WeilConjectures
