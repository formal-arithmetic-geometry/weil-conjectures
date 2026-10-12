/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal

/-!

# The pullback `g^*` of étale sheaves is braided

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A` in which
tensoring commutes with filtered colimits (e.g. `A` closed), the strong monoidal pullback `g^*`
on `A`-valued étale sheaves is braided: it is the strong monoidal left adjoint of the lax braided
pushforward `g_*`, for a monoidal adjunction (`CategoryTheory.Adjunction.μ_comp_map_braiding`).

## Main results

- `AlgebraicGeometry.Etale.upperStar_map_braiding_comp_δ`: the comparison map
  `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` is compatible with the braidings.
- `AlgebraicGeometry.Etale.braided_upperStar`: the pullback `g^*` is braided.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [(Y.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(Z.smallEtaleTopology.W (A := A)).IsMonoidal]
  [∀ M : A, PreservesFilteredColimitsOfSize.{u, u + 1} (tensorLeft M)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The comparison map `δ : g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the pullback of étale sheaves is
compatible with the braidings. -/
lemma Etale.upperStar_map_braiding_comp_δ (F G : Sheaf Y.smallEtaleTopology A) :
    (g)^*[A].map (β_ F G).hom ≫ δ (g)^*[A] G F =
      δ (g)^*[A] F G ≫ (β_ ((g)^*[A].obj F) ((g)^*[A].obj G)).hom :=
  (Etale.upperStarLowerStarAdjunction A g).map_braiding_comp_δ F G

/-- If tensoring in `A` commutes with filtered colimits (e.g. if `A` is closed), the pullback
`g^*` on étale sheaves is braided, its monoidal structure being `Etale.monoidal_upperStar`. -/
noncomputable instance Etale.braided_upperStar : (g)^*[A].Braided :=
  { Etale.monoidal_upperStar A g with
    braided := (Etale.upperStarLowerStarAdjunction A g).μ_comp_map_braiding }

example : (Etale.braided_upperStar A g).toMonoidal = Etale.monoidal_upperStar A g :=
  rfl

end AlgebraicGeometry
