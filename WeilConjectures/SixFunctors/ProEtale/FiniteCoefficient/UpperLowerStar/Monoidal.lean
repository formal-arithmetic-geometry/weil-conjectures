/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!

# The pushforward `g_*` and the pullback `g^*` are lax monoidal

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued pro-étale sheaves is lax braided. This is the general
statement for the pushforward along a continuous functor of sites, applied to the base
change functor; when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

The pullback `g^*` is (strong) monoidal, for a closed `A`. Its oplax structure maps are the
transposes of the lax structure maps of `g_*` along the adjunction `g^* ⊣ g_*`, and its lax
structure maps are their inverses; that these transposes are isomorphisms is `sorry`ed. The
lax monoidal structure is what is needed to pull back ring objects, module objects and their
global sections along `g` in `WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def`.

## Main results

- `AlgebraicGeometry.ProEtale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.
- `AlgebraicGeometry.ProEtale.monoidal_upperStar`: the pullback `g^*` is monoidal, with the
  oplax structure maps transposed from the lax structure maps of `g_*`.

## Sorried input

- `AlgebraicGeometry.ProEtale.isIso_η_upperStar` and
  `AlgebraicGeometry.ProEtale.isIso_δ_upperStar`: the transposed structure maps `g^* 𝟙 ⟶ 𝟙`
  and `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` are isomorphisms.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme ProEtale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)
  [((Scheme.ProEt.topology Y).W (A := A)).IsMonoidal]
  [((Scheme.ProEt.topology Z).W (A := A)).IsMonoidal]

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

/-- The pushforward `g_*` on pro-étale sheaves is lax monoidal, being the pushforward along
the continuous base change functor. -/
noncomputable instance ProEtale.laxMonoidal_lowerStar : (g)_*[A].LaxMonoidal := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The pushforward `g_*` on pro-étale sheaves is lax braided. When `A` is symmetric, this
says that `g_*` is lax symmetric monoidal. -/
noncomputable instance ProEtale.laxBraided_lowerStar : (g)_*[A].LaxBraided := by
  unfold ProEtale.lowerStar
  infer_instance

/-- The oplax monoidal structure on the pullback `g^*` obtained from the lax monoidal
structure of `g_*` by the adjunction `g^* ⊣ g_*`: the structure maps are the transposes
`g^* 𝟙 ⟶ 𝟙` of `ε : 𝟙 ⟶ g_* 𝟙` and `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` of
`(unit ⊗ unit) ≫ μ : F ⊗ G ⟶ g_* (g^* F ⊗ g^* G)`. They are isomorphisms
(`ProEtale.isIso_η_upperStar` and `ProEtale.isIso_δ_upperStar`), and the monoidal structure
`ProEtale.monoidal_upperStar` is built from their inverses; this is not an instance so that
the oplax structure of `g^*` is the one of `ProEtale.monoidal_upperStar` only. -/
@[instance_reducible]
noncomputable def ProEtale.upperStarOplaxMonoidal : (g)^*[A].OplaxMonoidal :=
  (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The pullback of the unit sheaf is the unit sheaf: the oplax unit map `g^* 𝟙 ⟶ 𝟙` of
`ProEtale.upperStarOplaxMonoidal` is an isomorphism. Together with
`ProEtale.isIso_δ_upperStar` this says that `g^*` is strong monoidal: `g^*` is the
sheafification of the left Kan extension along the opposite of base change of the
underlying presheaf; sheafification is monoidal, and the left Kan extension commutes with
the objectwise tensor product of presheaves because it is computed by filtered colimits
(base change preserves finite limits, so the comma categories indexing it are cofiltered)
and because the tensor product of the closed monoidal category `A` preserves colimits in
each variable. This filtered colimit argument is not formalized and the instance is
`sorry`ed; it is the monoidal counterpart of the sorried left exactness
`ProEtale.preservesFiniteLimits_op_lan_overPullback_of_isGrothendieckAbelian` of the same
Kan extension. -/
instance ProEtale.isIso_η_upperStar [MonoidalClosed A] :
    letI := ProEtale.upperStarOplaxMonoidal A g
    IsIso (Functor.OplaxMonoidal.η (g)^*[A]) :=
  sorry

/-- The pullback commutes with the tensor product of sheaves: the oplax structure map
`g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` of `ProEtale.upperStarOplaxMonoidal` is an isomorphism. See
`ProEtale.isIso_η_upperStar` for the mathematical argument and why it is `sorry`ed. -/
instance ProEtale.isIso_δ_upperStar [MonoidalClosed A]
    (F G : Sheaf (Scheme.ProEt.topology Y) A) :
    letI := ProEtale.upperStarOplaxMonoidal A g
    IsIso (Functor.OplaxMonoidal.δ (g)^*[A] F G) :=
  sorry

/-- The pullback `g^*` on pro-étale sheaves is (strong) monoidal, in particular lax monoidal
(`Functor.Monoidal.toLaxMonoidal`): its oplax structure maps are those of
`ProEtale.upperStarOplaxMonoidal`, transposed from the lax structure maps of `g_*` along
`g^* ⊣ g_*`, and its lax structure maps `𝟙 ⟶ g^* 𝟙` and `g^* F ⊗ g^* G ⟶ g^* (F ⊗ G)` are
their inverses, which exist by the sorried `ProEtale.isIso_η_upperStar` and
`ProEtale.isIso_δ_upperStar`. -/
noncomputable instance ProEtale.monoidal_upperStar [MonoidalClosed A] : (g)^*[A].Monoidal :=
  letI := ProEtale.upperStarOplaxMonoidal A g
  Functor.Monoidal.ofOplaxMonoidal _

end AlgebraicGeometry
