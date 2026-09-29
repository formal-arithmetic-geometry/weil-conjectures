/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# The pushforward `g_*` is lax symmetric monoidal, the pullback `g^*` is oplax monoidal

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued étale sheaves is lax braided. This is the general statement
for the pushforward along a continuous functor of sites, applied to the base change functor;
when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

Being left adjoint to the lax monoidal functor `g_*`, the pullback `g^*` is oplax monoidal,
with comparison maps `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` and `g^*𝟙 ⟶ 𝟙` adjoint to
`F ⊗ G ⟶ g_*g^*F ⊗ g_*g^*G ⟶ g_*(g^*F ⊗ g^*G)` and to the unit of `g_*`, and the
adjunction `g^* ⊣ g_*` is monoidal for these structures.

## Main results

- `AlgebraicGeometry.Etale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.
- `AlgebraicGeometry.Etale.oplaxMonoidal_upperStar`: the pullback `g^*` is oplax monoidal.
- `AlgebraicGeometry.Etale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction
  `g^* ⊣ g_*` is monoidal.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [(Y.smallEtaleTopology.W (A := A)).IsMonoidal]
  [(Z.smallEtaleTopology.W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` on étale sheaves is lax monoidal, being the pushforward along the
continuous base change functor. -/
noncomputable instance Etale.laxMonoidal_lowerStar : (g)_*[A].LaxMonoidal := by
  unfold Etale.lowerStar
  infer_instance

/-- The pushforward `g_*` on étale sheaves is lax braided. When `A` is symmetric, this says
that `g_*` is lax symmetric monoidal. -/
noncomputable instance Etale.laxBraided_lowerStar : (g)_*[A].LaxBraided := by
  unfold Etale.lowerStar
  infer_instance

/-- The pullback `g^*` on étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal pushforward `g_*`. -/
noncomputable instance Etale.oplaxMonoidal_upperStar : (g)^*[A].OplaxMonoidal :=
  (Etale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The adjunction `g^* ⊣ g_*` on étale sheaves is monoidal, for the oplax structure
`Etale.oplaxMonoidal_upperStar` on `g^*` and the lax structure `Etale.laxMonoidal_lowerStar`
on `g_*`. -/
instance Etale.isMonoidal_upperStarLowerStarAdjunction :
    (Etale.upperStarLowerStarAdjunction A g).IsMonoidal :=
  inferInstanceAs
    (letI := (Etale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal
    (Etale.upperStarLowerStarAdjunction A g).IsMonoidal)

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The comparison map `g^*(F ⊗ G) ⟶ g^*F ⊗ g^*G` of the oplax monoidal pullback `g^*` is
the pullback of `F ⊗ G ⟶ g_*g^*F ⊗ g_*g^*G ⟶ g_*(g^*F ⊗ g^*G)` followed by the counit. -/
lemma Etale.upperStar_δ_app (F G : Sheaf Y.smallEtaleTopology A) :
    δ (g)^*[A] F G =
      (g)^*[A].map (((Etale.upperStarLowerStarAdjunction A g).unit.app F ⊗ₘ
          (Etale.upperStarLowerStarAdjunction A g).unit.app G) ≫ μ (g)_*[A] _ _) ≫
        (Etale.upperStarLowerStarAdjunction A g).counit.app _ := by
  change ((Etale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm _ = _
  rw [Adjunction.homEquiv_counit]

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal in
/-- The comparison map `g^*𝟙 ⟶ 𝟙` of the oplax monoidal pullback `g^*` is the pullback of
the unit `𝟙 ⟶ g_*𝟙` of the lax monoidal pushforward followed by the counit. -/
lemma Etale.upperStar_η :
    η (g)^*[A] =
      (g)^*[A].map (ε (g)_*[A]) ≫ (Etale.upperStarLowerStarAdjunction A g).counit.app _ := by
  change ((Etale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm _ = _
  rw [Adjunction.homEquiv_counit]

end AlgebraicGeometry
