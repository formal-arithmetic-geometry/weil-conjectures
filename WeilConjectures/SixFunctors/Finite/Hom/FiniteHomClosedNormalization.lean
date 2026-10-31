/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Hom.FiniteHomNativeClosed

/-! The complete normalization of the etale closed record. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u a b w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

attribute [local irreducible] HasDerivedCategory.standard

attribute [local implicit_reducible] CategoryTheory.uniformProd
  Etale.sheafMonoidalCategory Etale.sheafBraidedCategory Etale.sheafMonoidalClosed

attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory.monoidalClosed_of_hasFunctorialFlatResolution
  DerivedCategory.monoidalClosed

private theorem native_normalized {C : Type a} [Category.{b} C]
    [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C] :
    (finiteHomClosed (C := C)).monoidal = (inferInstance : MonoidalCategory C) ∧
      ∀ P : C, HEq ((finiteHomClosed (C := C)).adjunction P)
        (finiteHomRightAdjunction P) := by
  exact ⟨rfl, fun _ ↦ HEq.rfl⟩

private theorem derived_normalized
    (C : Type a) [Category.{b} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    [CategoryTheory.Limits.HasColimitsOfSize.{0, 0} C] [HasDerivedCategory.{w} C]
    [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C] :
    FiniteHomDerivedClosedNormalization C (finiteHomNativeDerivedClosed C) := by
  let := finiteHomDerivedBraiding C
  dsimp only [finiteHomNativeDerivedClosed, FiniteHomDerivedClosedNormalization,
    finiteHomDerivedRightAdjunctionGeneral]
  exact native_normalized

/-- The uniquely normalized etale closed record is the native braided closed record.
Source: blueprint thm-coef-finite-hom, evaluation paragraph.
(blueprint: lem-coef-finite-hom-closed-normalization).

Proof: the native right-tensor adjunction and its natural evaluation satisfy the
normalization definition by reflexivity. Uniqueness in
finiteHomEtaleClosed_existsUnique identifies that record with its chosen witness.
The assertion concerns the entire record, including its fixed adjunctions. -/
theorem finiteHom_etale_closed_normalization
    (A : Type a) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) :
    finiteHomEtaleClosedGeneral A X =
      finiteHomNativeDerivedClosed (Sheaf X.smallEtaleTopology A) := by
  exact (finiteHomEtaleClosed_existsUnique A X).unique
    (finiteHomEtaleClosed_existsUnique A X).choose_spec.1
    (derived_normalized (Sheaf X.smallEtaleTopology A))

end WeilConjectures
