/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ModuleSubobjectGenericConstancy
import WeilConjectures.AlgebraicGeometry.ConstructibleClosedGenericCriterion

/-!
# Constructibility of module subsheaves over Noetherian rings

Source: Stacks Project, Proposition 09BH (3), proof of (3), and Lemma 095E.
This is the coefficient-hypothesis step of the curve devissage proof, without any
cohomology conclusion.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A subsheaf of a constructible module sheaf is constructible on a Noetherian scheme,
with coefficients in any Noetherian commutative ring.
Source: Stacks Project, Proposition 09BH (3), proof of (3), and Lemma 095E. -/
theorem constructible_of_mono_noetherian
    {X : Scheme.{u}} [IsNoetherian X] {Λ : Type (u + 1)} [CommRing Λ]
    [IsNoetherianRing Λ]
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (φ : F ⟶ G) [Mono φ] [IsConstructibleSheaf G] :
    IsConstructibleSheaf F := by
  apply constructible_of_closed_generic F
  intro Z i hi hZ
  have : IsClosedImmersion i := hi
  have : IsNoetherian Z := hZ
  have : IsConstructibleSheaf ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).obj G) :=
    IsConstructibleSheaf.upperStar i G
  exact exists_dense_open_of_mono_noetherian
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) i).map φ)

end AlgebraicGeometry.Scheme
