/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.SupportedExteriorShift
public import Sheaf.Paper.SupportedCupFunctoriality

/-! # SupportedTwistMultiplication

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-twist-degree-zero-product).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- Apply the existing degree-zero tensor comparison and a given sheaf multiplication
at a variable scheme, before specializing to the product scheme and the finite twists.
Source: blueprint Step 1, twist multiplication
(blueprint: def-pur-supported-twist-degree-zero-product). -/
def compactProductTwistMultiplicationCore (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] (X : Scheme.{u})
    {M N : DerivedCategory (Sheaf X.smallEtaleTopology C)}
    {S T U : Sheaf X.smallEtaleTopology C}
    (α : M ⟶ (DerivedCategory.singleFunctor _ 0).obj S)
    (β : N ⟶ (DerivedCategory.singleFunctor _ 0).obj T) (μ : S ⊗ T ⟶ U) :
    ((derivedTensor C X).obj M).obj N ⟶ (DerivedCategory.singleFunctor _ 0).obj U :=
  ((derivedTensor C X).map α).app N ≫ ((derivedTensor C X).obj _).map β ≫
    eqToHom (compactProductTensor_eq C X
      ((DerivedCategory.singleFunctor _ 0).obj S) ((DerivedCategory.singleFunctor _ 0).obj T)) ≫
    ProEtale.cupSingleTensorMap S T ≫ (DerivedCategory.singleFunctor _ 0).map μ

/-- Form the signed finite-twist multiplication with the coefficient ring and
annihilator still variable, retaining the dependency's actual normalized product.
Source: blueprint Step 1, twist multiplication
(blueprint: def-pur-supported-twist-degree-zero-product). -/
def compactProductTwistMultiplicationFinite (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (m : Γ(T, ⊤))) (r s : ℤ)
    {M N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (α : M ⟶ (DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf A m T hA r))
    (β : N ⟶ (DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf A m T hA s)) :=
  compactProductTwistMultiplicationCore (ModuleCat.{u + 1} A) T α β
    (functorialCupTwistProductGeneral A m hm hA T hT r s).hom

/-- Multiply two degree-zero twist representatives at a variable scheme.
Source: blueprint Step 1, twist multiplication
(blueprint: def-pur-supported-twist-degree-zero-product). -/
def compactProductTwistMultiplicationAt (P : PurityFiniteSetting.{u})
    (T : Scheme.{u}) (aT : T ⟶ Spec (.of P.field.k)) (r s : ℤ)
    {M N : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient))}
    (α : M ⟶ (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T r))
    (β : N ⟶ (DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false T s)) :=
  compactProductTwistMultiplicationFinite P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates T (P.diagonalExponent_isUnit aT) r s α β

end WeilConjectures.PurityFiniteSetting
