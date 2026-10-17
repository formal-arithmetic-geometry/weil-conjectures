/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Change of rings for the derived tensor product
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TensorProduct

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)

/-- The comparison `M ⊗_R P ⟶ (S ⊗_R M) ⊗_S P`, `m ⊗ p ↦ (1 ⊗ m) ⊗ p`, for an `R`-module `M`
and an `S`-module `P`, natural in `P`. -/
noncomputable def tensorRestrictScalarsHom (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) :
    M ⊗ (restrictScalars f).obj P ⟶ (restrictScalars f).obj ((extendScalars f).obj M ⊗ P) :=
  (extendRestrictScalarsAdj f).unit.app M ▷ _ ≫
    Functor.LaxMonoidal.μ (restrictScalars f) ((extendScalars f).obj M) P

set_option backward.isDefEq.respectTransparency false in
lemma tensorRestrictScalarsHom_tmul (M : ModuleCat.{u} R) (P : ModuleCat.{u} S) (m : M)
    (p : P) :
    tensorRestrictScalarsHom f M P (m ⊗ₜ p) = ((1 : S) ⊗ₜ[R, f] m) ⊗ₜ p := by
  simp [tensorRestrictScalarsHom]

end ModuleCat
