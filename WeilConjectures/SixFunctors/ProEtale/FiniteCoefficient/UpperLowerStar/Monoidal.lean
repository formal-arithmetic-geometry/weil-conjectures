/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs

/-!

# The pushforward `g_*` is lax symmetric monoidal

This is the pro-étale counterpart of
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal`.

For a morphism of schemes `g : Z ⟶ Y` and a braided monoidal coefficient category `A`, the
pushforward `g_*` on `A`-valued pro-étale sheaves is lax braided. This is the general
statement for the pushforward along a continuous functor of sites, applied to the base
change functor; when `A` is symmetric it says that `g_*` is lax symmetric monoidal.

## Main results

- `AlgebraicGeometry.ProEtale.laxBraided_lowerStar`: the pushforward `g_*` is lax braided.

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

end AlgebraicGeometry
