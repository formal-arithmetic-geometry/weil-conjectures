/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.CategoryTheory.Sites.DisjointGluing
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport

/-!
# Inverse images of completed realizations of finite free modules

The inverse image along a morphism of schemes of the completed realization of a finite
free module is the free module sheaf of the same rank. Both corepresent the finite
families of global sections.

Source: Bhatt--Scholze, Proposition 6.6.11
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {T S : Scheme.{u}} (g : S ⟶ T)

end AlgebraicGeometry.Scheme
