/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Étale localization of the derived categories of étale sheaves

Isomorphisms descend along surjective étale morphisms: for a surjective étale `u : U ⟶ X`, a
morphism `φ` of `D(X_ét, Λ)` with `Lu^* φ` invertible is invertible.

The localization of the exceptional inverse image along étale maps, `Lu^* Rf^! ≅ R(u ≫ f)^!`, is
in `WeilConjectures.SixFunctors.Etale.Derived.EtaleLocalizationUpperShriek`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_of_isIso_leftDerivedUpperStar_map_of_surjective`

## Implementation details

Pullback along `u` is exact, so it commutes with the cohomology sheaves, and the pullbacks along
the members of a jointly surjective family of étale maps reflect isomorphisms of sheaves. No
constructibility or finiteness hypothesis is needed.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Isomorphisms descend along étale surjections: if `u : U ⟶ X` is a surjective étale morphism
and `φ : M ⟶ N` a morphism of `D(X_ét, Λ)` such that `Lu^* φ` is an isomorphism, then so is `φ`.
-/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_surjective {U X : Scheme.{u}} (u : U ⟶ X)
    [Etale u] [Surjective u]
    {M N : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : M ⟶ N) (h : IsIso ((L((u)^*[ModuleCat.{u + 1} Λ])).map φ)) : IsIso φ := by
  have h' : IsIso (D((u)^*[ModuleCat.{u + 1} Λ]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ u) φ).1 h
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine Etale.isIso_of_isIso_upperStar_map_of_jointlySurjective (ModuleCat.{u + 1} Λ)
    (fun _ : PUnit.{u + 1} ↦ u) (fun x ↦ ⟨⟨⟩, u.surjective x⟩) _ fun _ ↦ ?_
  exact (NatIso.isIso_map_iff
    (((u)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((u)^*[ModuleCat.{u + 1} Λ]).map φ))

end Etale

end AlgebraicGeometry
