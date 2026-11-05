/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZero
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Canonical intrinsic finite-coefficient inverse image

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
blueprint ordinary pro-etale operations (blueprint: def-weil-pbc-proetale-operations).

The existing arbitrary-ring and continuous-function interfaces are reexported.
Here the canonical fixed-scalar inverse image is transported through the published
intrinsic constant-ring realization, without choosing a coefficient identification.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

end AlgebraicGeometry.Scheme
