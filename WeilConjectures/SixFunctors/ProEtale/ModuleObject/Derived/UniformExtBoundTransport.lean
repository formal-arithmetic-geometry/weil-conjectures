/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

/-!
# Transport of the uniform `Ext` bound along isomorphisms of coefficient rings

The property `ProEtale.HasUniformConstructibleExtBound R` of a ring object `R` of abelian sheaves
on `X_proét` (blueprint `sk-lem-uniform-constructible-ext`) only depends on `R` up to
isomorphism of ring objects (`ProEtale.HasUniformConstructibleExtBound.of_isIso`): restriction of
scalars along an isomorphism `φ : R ⟶ S` is an equivalence `Mod S ≌ Mod R` which preserves
constructibility, and so is its levelwise extension to the derived categories.

This lets us transfer the bound between the coefficient rings `E̲`, `𝒪̲_E` attached to an abstract
finite extension `E` of `ℚ_ℓ` and those attached to a finite subextension of `ℚ̄_ℓ`, for which the
integral and rational theory is developed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable {X : Scheme.{u}} {R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}} [MonObj R] [MonObj S]

/-- Restriction of scalars along an isomorphism of ring objects preserves constructibility. -/
lemma IsConstructibleModuleObject.comap_of_isIso (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S}
    (hM : IsConstructibleModuleObject S M) :
    IsConstructibleModuleObject R ((Mod.comap φ).obj M) :=
  sorry

/-- The uniform `Ext` bound is invariant under isomorphisms of ring objects. -/
theorem HasUniformConstructibleExtBound.of_isIso (φ : R ⟶ S) [IsMonHom φ] [IsIso φ]
    (h : HasUniformConstructibleExtBound S) : HasUniformConstructibleExtBound R :=
  sorry

end AlgebraicGeometry.ProEtale
