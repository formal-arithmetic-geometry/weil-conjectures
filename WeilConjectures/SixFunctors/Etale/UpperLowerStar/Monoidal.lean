/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!

# The pushforward `g_*` is lax symmetric monoidal

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued étale sheaves is lax braided. This is the general statement
for the pushforward along a continuous functor of sites, applied to the base change functor;
when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

## Main results

- `AlgebraicGeometry.Etale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.

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

end AlgebraicGeometry
