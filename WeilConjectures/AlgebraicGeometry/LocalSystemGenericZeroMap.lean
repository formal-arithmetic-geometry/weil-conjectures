/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.AlgebraicGeometry.GenericStalkVanishingPropagation
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! # Generic detection of maps into a local system -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A morphism into a local system vanishes if it vanishes at the geometric generic point
(Stacks, Tags 09BG and 09BH). -/
theorem eq_zero_of_generic_sheafFiber_eq_zero
    {X : Scheme.{u}} [IrreducibleSpace X] {Λ : Type (u + 1)} [CommRing Λ]
    (η : X) (hη : IsGenericPoint η Set.univ)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    [IsLocallyConstantSheaf G] (φ : F ⟶ G)
    (hφ : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
      s (IsLocalRing.closedPoint Ω) = η → (pointSmallEtale s).sheafFiber.map φ = 0) :
    φ = 0 := by
  have : Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  apply sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  have : ((pointSmallEtale (X.algClosurePoint x)).sheafFiber
      (A := ModuleCat.{u + 1} Λ)).Additive :=
    (pointSmallEtale (X.algClosurePoint x)).sheafFiber_additive
  simpa only [Functor.map_zero] using
    all_sheafFiber_map_eq_zero_of_generic η hη φ hφ _ (X.algClosurePoint x)

end AlgebraicGeometry.Scheme
