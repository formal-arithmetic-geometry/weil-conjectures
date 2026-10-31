/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenInterchangeReduction.ProperOpenLambdaOrdinarySquare
import WeilConjectures.SixFunctors.GeneratorReduction.ShortWordCompletionIsomorphism
import Mathlib.CategoryTheory.Adjunction.Mates

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u s i
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.GeneratorReduction
namespace WeilConjectures.OpenInterchangeReduction

private theorem inverseOrZero_eq_inv {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y : A} (f : X ⟶ Y) [IsIso f] : inverseOrZero f = inv f := by
  classical
  simp only [inverseOrZero, dif_pos (inferInstance : IsIso f)]

private theorem inverse_square {A : Type*} [Category A] [HasZeroMorphisms A]
    {X Y X' Y' : A} (f : X ⟶ Y) (g : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso a] [IsIso b] (h : f ≫ b = a ≫ g) :
    g ≫ inverseOrZero b = inverseOrZero a ≫ f := by
  rw [inverseOrZero_eq_inv, inverseOrZero_eq_inv]
  apply (cancel_epi a).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private theorem inverse_naturality {A N : Type*} [Category A] [Category N]
    [HasZeroMorphisms N] {F G : A ⥤ N} (α : F ⟶ G) {X Y : A} (f : X ⟶ Y)
    [IsIso (α.app X)] [IsIso (α.app Y)] :
    G.map f ≫ inverseOrZero (α.app Y) = inverseOrZero (α.app X) ≫ F.map f := by
  apply inverse_square
  exact α.naturality f

end WeilConjectures.OpenInterchangeReduction
