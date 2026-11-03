/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
public import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsFlat
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import WeilConjectures.SixFunctors.Etale.Derived.CoextendScalars
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Reduction
import WeilConjectures.CategoryTheory.Sites.FixedCoefficientDerivedChangeOfRings
import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal
import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction
import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Basic

/-! # A principal coefficient comparison

Source: latest blueprint lem-fix-operation-reduction, proof of the principal
coefficient-change comparisons. The coefficient quotient has a finite free
resolution; its extension functor is the constructed fixed scalar adjoint.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory Opposite MonoidalCategory
open scoped CategoryTheory.Functor
attribute [local instance 2000] CommRing.toRing
namespace AlgebraicGeometry.PrincipalCoefficient
set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- Tensoring with the shifted unit is the shift, naturally in the other factor. -/
private def tensorRightShiftUnitIso
    {C : Type*} [Category C] [MonoidalCategory C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [(curriedTensor C).CommShift₂Int] (n : ℤ) :
    tensorRight ((𝟙_ C)⟦n⟧) ≅ shiftFunctor C n :=
  NatIso.ofComponents
    (fun K ↦ ((tensorLeft K).commShiftIso n).app (𝟙_ C) ≪≫
      (shiftFunctor C n).mapIso (ρ_ K)) (by
    intro K L f
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
    change (f ▷ (𝟙_ C)⟦n⟧) ≫
        ((tensorLeft L).commShiftIso n).hom.app (𝟙_ C) ≫
        (shiftFunctor C n).map (ρ_ L).hom =
      ((tensorLeft K).commShiftIso n).hom.app (𝟙_ C) ≫
        (shiftFunctor C n).map (ρ_ K).hom ≫ (shiftFunctor C n).map f
    have hn := NatTrans.shift_app_comm ((curriedTensor C).map f) n (𝟙_ C)
    simp only [curriedTensor_map_app] at hn
    rw [← Category.assoc, ← hn]
    simp only [Category.assoc]
    rw [← Functor.map_comp, ← Functor.map_comp, rightUnitor_naturality])

/-- Combine the two coefficient computations before using a geometric adjunction. -/
private theorem coinductionShiftIso
    {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u})
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    Nonempty ((Etale.coextendScalars
      (Ideal.Quotient.mk (Ideal.span {a} ^ n)) X).rightDerivedFunctor.obj K ≅
      ((extension X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj
        K)⟦(-1 : ℤ)⟧) := by
  exact ⟨(principalCoinductionTensor ha n X K).some.symm ≪≫
    tensorIso (Iso.refl _) (principalCoinductionUnit ha n X).some ≪≫
      (tensorRightShiftUnitIso (-1 : ℤ)).app _⟩

/-- The zero coefficient category remains zero after passage to the derived category. -/
private theorem isZero_derived_of_subsingleton
    {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
    (J : GrothendieckTopology C) (B : Type (u + 1)) [CommRing B] [Subsingleton B]
    (K : DerivedCategory (Sheaf J (ModuleCat.{u + 1} B))) :
    CategoryTheory.Limits.IsZero K := by
  apply DerivedCategory.isZero_of_forall_isZero
  intro F
  apply Sheaf.isZero_of_isZero_obj
  intro U
  let := Module.subsingleton B (F.obj.obj U)
  exact ModuleCat.isZero_of_subsingleton _


/-- Principal exceptional comparison.
Source: latest blueprint lem-fix-operation-reduction
(blueprint: lem-principal-coefficient-exceptional).

Proof: Derived restriction R has a right adjoint H, derived coextension. For the
regular quotient B = A/(a^n), the two-term free resolution identifies the coefficient
dual RHom_A(B,A) with B shifted by -1, as a B-module. The perfect tensor-Hom
comparison therefore identifies H with fixed scalar extension shifted by -1,
including its B-action. Restriction commutes with compact support: for the proper
factor transpose the scalar/pullback square, and for the open factor use exact
extension by zero. Taking right adjoints gives H_X G_A isomorphic to G_B H_Y.
Substitute the shifted-extension identifications, commute the exceptional right
adjoint with the shift, and cancel the common shift. All adjunctions are the
specified ones, identified by counit-compatible uniqueness. At exponent zero the
quotient is zero, so all the displayed coefficient functors are zero. -/
theorem principalExceptional {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).IsLeftAdjoint] (L : DE(Y, A)) :
    Nonempty ((extension X.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).rightAdjoint.obj L) ≅
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n))
      f).rightAdjoint.obj
        ((extension Y.smallEtaleTopology (Ideal.Quotient.mk (Ideal.span {a} ^ n))).obj L)) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (A ⧸ Ideal.span {a} ^ 0) :=
      (Ideal.Quotient.subsingleton_iff).2 (by simp)
    exact ⟨(isZero_derived_of_subsingleton _ _ _).iso
      (isZero_derived_of_subsingleton _ _ _)⟩
  · let φ := Ideal.Quotient.mk (Ideal.span {a} ^ n)
    let FA := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f
    let FB := Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f
    let aA := Adjunction.ofIsLeftAdjoint FA
    let aB := Adjunction.ofIsLeftAdjoint FB
    let aX := Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
    let aY := Adjunction.mapDerivedCategoryRightDerivedAdjunction
      (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ)
    let h := conjugateIsoEquiv (aX.comp aA) (aB.comp aY)
      (compactSupportRestrictionIso φ f).some.symm
    let := aB.rightAdjointCommShift ℤ
    let e :
        ((extension X.smallEtaleTopology φ).obj (FA.rightAdjoint.obj L))⟦(-1 : ℤ)⟧ ≅
        (FB.rightAdjoint.obj ((extension Y.smallEtaleTopology φ).obj L))⟦(-1 : ℤ)⟧ :=
      (coinductionShiftIso ha n X (FA.rightAdjoint.obj L)).some.symm ≪≫
        h.app L ≪≫ FB.rightAdjoint.mapIso (coinductionShiftIso ha n Y L).some ≪≫
        (FB.rightAdjoint.commShiftIso (-1 : ℤ)).app
          ((extension Y.smallEtaleTopology φ).obj L)
    exact ⟨(shiftFunctor _ (-1 : ℤ)).preimageIso e⟩

end AlgebraicGeometry.PrincipalCoefficient
