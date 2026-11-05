/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicAlgClColimit

/-!
# Restriction of scalars of an extension of scalars to a colimit of algebras

Let `C` be a braided monoidal category whose tensor product preserves colimits, `R` a commutative
algebra object and `M` an `R`-module object. For a morphism of algebras `s : S ⟶ S'` under `R`,
the map `S ⊗_R M ⟶ S' ⊗_R M` is `R`-linear (`CategoryTheory.Mod.restrictExtendChange`).

If `T = colim_j S_j` is a colimit of `R`-algebras, then `Res_R(T ⊗_R M) = colim_j Res_R(S_j ⊗_R M)`
as `R`-module objects (`CategoryTheory.Mod.isColimitRestrictExtendScalarsColimitCocone`), the
forgetful functor from `R`-module objects reflecting colimits.
-/

@[expose] public section

universe v₁ u₁

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)] [BraidedCategory C]
  {R : C} [MonObj R] [IsCommMonObj R]

section Change

variable {S S' : C} [MonObj S] [MonObj S'] {φ : R ⟶ S} {φ' : R ⟶ S'} [IsMonHom φ]
  [IsMonHom φ'] (s : S ⟶ S') [IsMonHom s] (h : φ ≫ s = φ') (M : Mod C R)

end Change

section Colimit

variable {J : Type} [SmallCategory J] (S : J ⥤ C) [∀ j, MonObj (S.obj j)]
  [∀ {j k : J} (g : j ⟶ k), IsMonHom (S.map g)] (φ : ∀ j, R ⟶ S.obj j) [∀ j, IsMonHom (φ j)]
  (hφ : ∀ {j k : J} (g : j ⟶ k), φ j ≫ S.map g = φ k) (M : Mod C R)

variable {T : C} [MonObj T] (ι : ∀ j, S.obj j ⟶ T)
  (hι : ∀ {j k : J} (g : j ⟶ k), S.map g ≫ ι k = ι j)
  [∀ j, IsMonHom (ι j)] (ψ : R ⟶ T) [IsMonHom ψ] (hψ : ∀ j, φ j ≫ ι j = ψ)

end Colimit

end CategoryTheory.Mod
