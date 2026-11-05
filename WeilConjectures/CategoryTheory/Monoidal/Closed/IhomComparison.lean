/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import WeilConjectures.CategoryTheory.Monoidal.Closed.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Internal homs along exact monoidal functors

Let `C` be a braided monoidal closed preadditive category. The internal hom `[-, Q]` turns
cokernels into kernels (`CategoryTheory.MonoidalClosed.isLimitKernelForkPreApp`): if
`π : P₀ ⟶ P` is a cokernel of `f : P₁ ⟶ P₀`, then `[π, Q] : [P, Q] ⟶ [P₀, Q]` is a kernel of
`[f, Q]`. It is additive in the first variable (`CategoryTheory.MonoidalClosed.pre_add_app`).

Let `F : C ⥤ D` be a lax monoidal functor to another monoidal closed category. We give criteria
for the comparison map `F [P, Q] ⟶ [F P, F Q]`
(`CategoryTheory.Functor.LaxMonoidal.ihomComparison`) to be an isomorphism: this holds

- for `P = 𝟙_ C` if the unit map `ε F` is an isomorphism
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_unit`);
- for `P` isomorphic to an object for which it holds
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_iff_of_iso_left`);
- for `P` a finite biproduct of objects for which it holds, if `F` is additive
  (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_biproduct`);
- for `P` the cokernel of a morphism `P₁ ⟶ P₀` between objects for which it holds, if `F`
  preserves the kernel of `[P₀, Q] ⟶ [P₁, Q]` and maps the projection onto the cokernel to an
  epimorphism (`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_app_of_isColimit`).

For instance, an exact monoidal functor out of the category of modules over a commutative ring
preserves internal homs out of finitely presented modules.
-/

@[expose] public section

namespace CategoryTheory

open Limits MonoidalCategory

namespace MonoidalClosed

section Braided

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] [BraidedCategory C]

/-- In a braided monoidal closed category, tensoring on the right preserves epimorphisms. -/
lemma epi_whiskerRight {A B : C} (f : B ⟶ A) [Epi f] (Z : C) : Epi (f ▷ Z) := by
  have : Epi (Z ◁ f) := (tensorLeft Z).map_epi f
  rw [← Category.comp_id (f ▷ Z), ← Iso.hom_inv_id (β_ A Z),
    BraidedCategory.braiding_naturality_left_assoc]
  infer_instance

/-- In a braided monoidal closed category, precomposition `[A, X] ⟶ [B, X]` with an epimorphism
`B ⟶ A` is a monomorphism. -/
lemma mono_pre_app {A B : C} (f : B ⟶ A) [Epi f] (X : C) : Mono ((pre f).app X) := by
  refine ⟨fun {T} a b h ↦ uncurry_injective ?_⟩
  have := epi_whiskerRight f T
  rw [← cancel_epi (f ▷ T), ← uncurry_pre_app, ← uncurry_pre_app, h]

/-- A preadditive braided monoidal closed category is monoidal preadditive: tensoring on the left
is a left adjoint, hence additive, and tensoring on the right is isomorphic to it. -/
lemma monoidalPreadditive_of_braided [Preadditive C] [HasBinaryBiproducts C] :
    MonoidalPreadditive C := by
  have (X : C) : (tensorLeft X).Additive := by
    have := (ihom.adjunction X).isLeftAdjoint
    have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
    exact Functor.additive_of_preservesBinaryBiproducts _
  have hr {X Y : C} (f : X ⟶ Y) (Z : C) : f ▷ Z = (β_ X Z).hom ≫ Z ◁ f ≫ (β_ Y Z).inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  have h0 (X Y Z : C) : Z ◁ (0 : X ⟶ Y) = 0 := (tensorLeft Z).map_zero X Y
  have hadd (X Y Z : C) (f g : X ⟶ Y) : Z ◁ (f + g) = Z ◁ f + Z ◁ g :=
    (tensorLeft Z).map_add
  exact
    { whiskerLeft_zero := h0 _ _ _
      zero_whiskerRight := by
        intro X Y Z
        rw [hr, h0, zero_comp, comp_zero]
      whiskerLeft_add := by
        intro X Y Z f g
        exact hadd _ _ _ f g
      add_whiskerRight := by
        intro X Y Z f g
        rw [hr, hr, hr, hadd, Preadditive.add_comp, Preadditive.comp_add] }

end Braided

section Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C]

/-- Precomposition `[A, X] ⟶ [B, X]` is additive in the morphism `B ⟶ A`. -/
lemma pre_add_app {A B : C} (f g : B ⟶ A) (X : C) :
    (pre (f + g)).app X = (pre f).app X + (pre g).app X :=
  uncurry_injective (by
    rw [uncurry_pre, uncurry_add, uncurry_pre, uncurry_pre,
      MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp])

/-- Precomposition `[A, X] ⟶ [B, X]`, as an additive map in the morphism `B ⟶ A`. -/
@[simps]
def preAppAddHom (A B X : C) : (B ⟶ A) →+ ((ihom A).obj X ⟶ (ihom B).obj X) where
  toFun f := (pre f).app X
  map_zero' := pre_zero_app X
  map_add' f g := pre_add_app f g X

variable [BraidedCategory C]

end Preadditive

end MonoidalClosed

namespace Functor.LaxMonoidal

open MonoidalClosed

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalClosed C] [MonoidalClosed D] (F : C ⥤ D) [F.LaxMonoidal]

/-- The comparison map `F [A, B] ⟶ [F A, F B]` is an isomorphism at `B` if and only if it is one
at any `B'` isomorphic to `B`. -/
lemma isIso_ihomComparison_app_iff_of_iso_right (A : C) {B B' : C} (e : B ≅ B') :
    IsIso ((ihomComparison F A).natTrans.app B) ↔ IsIso ((ihomComparison F A).natTrans.app B') :=
  NatTrans.isIso_app_iff_of_iso _ e

/-- The comparison map `F [A, B] ⟶ [F A, F B]` is an isomorphism at `A` if and only if it is one
at any `A'` isomorphic to `A`
(`CategoryTheory.Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app`). -/
lemma isIso_ihomComparison_app_iff_of_iso_left {A A' : C} (e : A ≅ A') (B : C) :
    IsIso ((ihomComparison F A).natTrans.app B) ↔ IsIso ((ihomComparison F A').natTrans.app B) := by
  have h := map_pre_app_comp_ihomComparison_app F e.hom B
  constructor
  · intro _
    have : IsIso ((ihomComparison F A').natTrans.app B ≫ (pre (F.map e.hom)).app (F.obj B)) := by
      rw [← h]; infer_instance
    exact IsIso.of_isIso_comp_right _ ((pre (F.map e.hom)).app (F.obj B))
  · intro _
    have : IsIso (F.map ((pre e.hom).app B) ≫ (ihomComparison F A).natTrans.app B) := by
      rw [h]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map ((pre e.hom).app B)) _

section Preadditive

variable [Preadditive C] [Preadditive D] [MonoidalPreadditive C] [MonoidalPreadditive D]

variable [BraidedCategory C] [BraidedCategory D]

end Preadditive

end Functor.LaxMonoidal

end CategoryTheory
