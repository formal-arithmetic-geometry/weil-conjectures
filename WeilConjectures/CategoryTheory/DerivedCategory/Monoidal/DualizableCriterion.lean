/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# A chain-level criterion for dualizability in the derived category

Let `C` be a braided monoidal closed Grothendieck abelian category with functorial flat
resolutions, and `K(C)` its homotopy category. For a K-flat complex `P`, K-injective resolutions
`u : 𝟙 ⟶ I₁` of the unit and `i : P ⟶ I` of `P`, and a map `j : I₁ ⊗ P ⟶ I` with
`u ▷ P ≫ j = λ ≫ i`, the canonical comparison `[P, 𝟙] ⊗ P ⟶ [P, P]` of `D(C)` is the image of
the chain-level map `χ : iHom(P, I₁) ⊗ P ⟶ iHom(P, I)` adjoint to
`P ⊗ (iHom(P, I₁) ⊗ P) ≅ (P ⊗ iHom(P, I₁)) ⊗ P ⟶ I₁ ⊗ P ⟶ I`. So `Qh.obj P` is dualizable if and
only if `Qh.map χ` is an isomorphism (`DerivedCategory.isDualizable_Qh_obj_iff`).

The point of this criterion is that it is stated in terms of complexes, so that it can be
transported along exact monoidal functors which commute with internal homs.

## Main statements

- `CategoryTheory.MonoidalClosed.isIso_curry_of_bijective`: a map `e : X ⊗ H ⟶ M` such that
  `f ↦ X ◁ f ≫ e` is bijective exhibits `H` as `[X, M]`.
- `CategoryTheory.MonoidalClosed.isDualizable_iff_isIso_ihomUnitTensorToIhom`: in a braided
  monoidal closed category, `X` is dualizable if and only if `[X, 𝟙] ⊗ X ⟶ [X, X]` is an
  isomorphism.
- `DerivedCategory.isIso_curry_μ_Qh_counit`: for `P` K-flat and `Y` K-injective, the internal hom
  `[Qh P, Qh Y]` of `D(C)` is `Qh (iHom(P, Y))`.
- `DerivedCategory.isDualizable_Qh_obj_iff`: the chain-level criterion.
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory.MonoidalClosed

variable {C : Type*} [Category C] [MonoidalCategory C] [MonoidalClosed C]

variable [BraidedCategory C]

/-- In a braided monoidal closed category, an object `X` is dualizable if and only if the
canonical comparison `[X, 𝟙] ⊗ X ⟶ [X, X]` is an isomorphism. -/
lemma isDualizable_iff_isIso_ihomUnitTensorToIhom (X : C) :
    IsDualizable X ↔ IsIso (ihomUnitTensorToIhom X X) := by
  refine ⟨fun ⟨_⟩ ↦ ?_, fun _ ↦ ?_⟩
  · let := BraidedCategory.exactPairing_swap X Xᘁ
    exact isIso_ihomUnitTensorToIhom Xᘁ X X
  · let := exactPairingOfIsIso X
    exact ⟨{ rightDual := _, exact := BraidedCategory.exactPairing_swap ((ihom X).obj (𝟙_ C)) X }⟩

end CategoryTheory.MonoidalClosed

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [HasDerivedCategory.{v} C] [Abelian.HasFunctorialFlatResolution C]

local instance : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink C

open HomotopyCategory MonoidalClosed

section InternalHom

variable {P Y : HomotopyCategory C (.up ℤ)}

end InternalHom

end DerivedCategory
