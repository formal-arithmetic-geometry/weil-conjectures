/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic

/-!

# Functorial flat resolutions of étale sheaves (sorried)

The K-flat left derivability structure computes the derived pullback on a K-flat
resolution, so it requires the sheaf categories to admit functorial flat resolutions
for the monoidal structure of
`WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs`. For module
coefficients these are given by the functorial local free covers `⊕ j_{U!} Λ_U`
(Stacks Project, Tag 06YL); the construction is not yet formalized and the instance is
recorded with `sorry`.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace AlgebraicGeometry

open Scheme

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

variable (Y : Scheme.{u})

variable [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

/-- Functorial flat resolutions of étale sheaves: for module coefficients these are
given by the functorial local free covers `⊕ j_{U!} Λ_U` (Stacks Project, Tag 06YL). -/
instance Etale.sheafHasFunctorialFlatResolution
    [Abelian.HasFunctorialFlatResolution A] :
    Abelian.HasFunctorialFlatResolution (Sheaf Y.smallEtaleTopology A) :=
  sorry

end AlgebraicGeometry
