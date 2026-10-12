/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Derived.ExtendScalars
public import WeilConjectures.SixFunctors.ProEtale.Derived.OpenImmersionLowerShriek

/-!
# Derived scalar extension commutes with extension by zero

Let `S` be an algebra over a commutative ring `R` and `j : U ⟶ X` an open immersion. Derived
scalar extension `Ψ = - ⊗ᴸ_R S` commutes with the exact extension by zero `j_!`:
`Ψ (j_! K) ≅ j_! (Ψ K)` (blueprint `thm-trf-finite-coefficient-map`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S]

section OpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Derived scalar extension commutes with the extension by zero along an open immersion `j`:
`Ψ (j_! K) ≅ j_! (Ψ K)`. -/
noncomputable def openImmersionLowerShriekExtendScalarsIso :
    D((j)_!open[ModuleCat.{u + 1} R]) ⋙ L(sheafExtendScalars (algebraMap R S) X) ≅
      L(sheafExtendScalars (algebraMap R S) U) ⋙ D((j)_!open[ModuleCat.{u + 1} S]) :=
  sorry

end OpenImmersion
end AlgebraicGeometry.ProEtale
