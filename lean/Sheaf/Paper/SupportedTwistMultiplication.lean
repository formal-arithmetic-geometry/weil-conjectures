/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.SupportedTwistDegreeZeroProduct
public import Sheaf.Paper.SupportedTwistPullback

/-! # SupportedTwistMultiplication

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-supported-twist-multiplication).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v c d e w v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting

open AlgebraicGeometry AlgebraicGeometry.Etale

/-- The ordinary exterior object is its defining pullback-tensor object.
Source: blueprint Step 1, exterior product convention
(blueprint: def-pur-supported-twist-multiplication).
Proof: unfold externalProduct; its definition is exactly the displayed object. -/
theorem compactProductExterior_eq (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasSmallSiteSheafify C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology C)) :
    externalProduct C f g K L =
      ((derivedTensor C (pullback f g)).obj
        ((upperStar C (pullback.fst f g)).leftDerivedFunctor.obj K)).obj
        ((upperStar C (pullback.snd f g)).leftDerivedFunctor.obj L) := by
  sorry

/-- Assemble the two canonical twist pullbacks and degree-zero multiplication before
specializing the coefficient ring or annihilator.
Source: blueprint Step 1, exterior twist multiplication
(blueprint: def-pur-supported-twist-multiplication). -/
def compactProductTwistMultiplicationGeneral (A : Type (u + 1)) [CommRing A]
    (m : ℕ) (hm : 0 < m) (hA : (m : A) = 0)
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    (hX : IsUnit (m : Γ(X, ⊤))) (hY : IsUnit (m : Γ(Y, ⊤)))
    (hP : IsUnit (m : Γ(pullback f g, ⊤))) (r s : ℤ) :
    externalProduct (ModuleCat.{u + 1} A) f g
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A m X hA r))
      ((DerivedCategory.singleFunctor _ 0).obj (Scheme.finiteEtaleTateSheaf A m Y hA s)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj
      (Scheme.finiteEtaleTateSheaf A m (pullback f g) hA (r + s)) :=
  eqToHom (compactProductExterior_eq (ModuleCat.{u + 1} A) f g _ _) ≫
    compactProductTwistMultiplicationFinite A m hm hA (pullback f g) hP r s
      (compactProductTwistPullbackCore (ModuleCat.{u + 1} A) (pullback.fst f g)
        (Scheme.finiteEtaleTateSheaf A m X hA r)
        (Scheme.finiteEtaleTateSheaf A m (pullback f g) hA r)
        (p1DecompositionSheafPullback A m hm hA (pullback.fst f g) hX r).hom)
      (compactProductTwistPullbackCore (ModuleCat.{u + 1} A) (pullback.snd f g)
        (Scheme.finiteEtaleTateSheaf A m Y hA s)
        (Scheme.finiteEtaleTateSheaf A m (pullback f g) hA s)
        (p1DecompositionSheafPullback A m hm hA (pullback.snd f g) hY s).hom)

/-- The specified multiplication of the pulled-back finite twists.
Source: blueprint Step 1, K exterior L identified with A(r+s)
(blueprint: def-pur-supported-twist-multiplication). -/
def compactProductTwistMultiplication (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)) (r s : ℤ) :
    externalProduct (ModuleCat.{u + 1} P.Coefficient) f g
      ((DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false X r))
      ((DerivedCategory.singleFunctor _ 0).obj (P.functorialCupTwist false Y s)) ⟶
    (DerivedCategory.singleFunctor _ 0).obj
      (P.functorialCupTwist false (pullback f g) (r + s)) :=
  compactProductTwistMultiplicationGeneral P.Coefficient P.diagonalExponent
    (pow_pos (Fact.out : P.coefficients.l.Prime).pos P.level)
    P.diagonalExponent_annihilates f g (P.diagonalExponent_isUnit f)
    (P.diagonalExponent_isUnit g) (P.diagonalExponent_isUnit (pullback.toBase f g)) r s


end WeilConjectures.PurityFiniteSetting
