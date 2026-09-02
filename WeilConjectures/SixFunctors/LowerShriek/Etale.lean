/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.LowerShriek.Defs
public import WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale

/-!

# Lower shriek on small étale sites

For a morphism `f : X ⟶ Y` admitting a compactification, the general lower shriek of
`WeilConjectures.SixFunctors.LowerShriek.Defs` (with `P = Q = @Etale`) specializes to the
small étale sites. This file records the resulting functor
`f_! : Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A`.

All site-theoretic inputs of the general definition are discharged here:

- `@IsOpenImmersion ≤ @Etale` holds since open immersions are étale.
- The Kan extension hypothesis holds by the instance of
  `WeilConjectures.SixFunctors.LowerShriek.OpenImmersion.Etale`, the abelian `A` having an
  initial object.
- The continuity of the base change functor along an *arbitrary* morphism is provided by
  the instance `Etale.isContinuous_overPullback` of
  `WeilConjectures.SixFunctors.UpperLowerStar.Etale`.
- Sheafification on the small étale sites is provided by the sorried instance of
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify`.

Hence `f_!` carries no hypotheses beyond the standing assumptions on `A`.

## Main definitions

- `AlgebraicGeometry.isOpenImmersion_le_etale`: open immersions are étale, as an
  inequality of morphism properties.
- `AlgebraicGeometry.Etale.lowerShriek`: the lower shriek `f_!` on étale sheaves along a
  morphism admitting a compactification.
- `AlgebraicGeometry.Etale.lowerShriek_eq`: the lower shriek `f_!` is the extension by zero
  along the open immersion of the chosen compactification followed by the pushforward
  `Etale.lowerStar` along its proper structure morphism.
- `AlgebraicGeometry.Etale.preservesFiniteLimits_lowerShriek`: the lower shriek `f_!` with
  values in an abelian category is left exact. This one needs sheafification to be *exact*,
  not merely to exist.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- Open immersions are étale, as an inequality of morphism properties. -/
lemma isOpenImmersion_le_etale : @IsOpenImmersion ≤ @Etale := fun _ _ _ hi =>
  have : IsOpenImmersion _ := hi
  inferInstance

section LowerShriek

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [SmallSiteCoefficients A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]

open Etale

/-- The lower shriek `f_!` along a morphism `f : X ⟶ Y` admitting a compactification on
sheaves for the small étale sites. -/
noncomputable def Etale.lowerShriek :
    Sheaf X.smallEtaleTopology A ⥤ Sheaf Y.smallEtaleTopology A :=
  AlgebraicGeometry.lowerShriek A @Etale @Etale le_rfl f isOpenImmersion_le_etale

/-- The lower shriek `f_!` on étale sheaves is the extension by zero along the open
immersion of the chosen compactification followed by the pushforward `Etale.lowerStar`
along its proper structure morphism. -/
lemma Etale.lowerShriek_eq :
    Etale.lowerShriek A f =
      ((HasCompactification.compactification f).i)_!open[A] ⋙
        ((HasCompactification.compactification f).g)_*[A] :=
  rfl

/-- The lower shriek `f_!` on étale sheaves with values in a preadditive category is
additive, being the composition of the extension by zero along the open immersion of the
chosen compactification with the pushforward along its proper structure morphism. -/
instance Etale.lowerShriek_additive : (Etale.lowerShriek A f).Additive := by
  rw [Etale.lowerShriek_eq]
  infer_instance

/-- The lower shriek `f_!` on étale sheaves with values in an abelian category is left
exact, being the composition of the exact extension by zero along the open immersion of
the chosen compactification with the left exact pushforward along its proper structure
morphism.

The extension by zero is sheafification composed with a left Kan extension, so left
exactness of sheafification is needed here; see
`AlgebraicGeometry.Etale.preservesFiniteLimits_openImmersionLowerShriek`. This is why
`HasSheafify` appears in addition to the `HasWeakSheafify` that defines `f_!`. -/
instance Etale.preservesFiniteLimits_lowerShriek :
    PreservesFiniteLimits (Etale.lowerShriek A f) := by
  rw [Etale.lowerShriek_eq]
  exact comp_preservesFiniteLimits _ _

end LowerShriek

--TODO: the composition isomorphism : `(fg)_! ≅ f_! g_!`

--TODO: invarience with choice of compcatification

end AlgebraicGeometry
