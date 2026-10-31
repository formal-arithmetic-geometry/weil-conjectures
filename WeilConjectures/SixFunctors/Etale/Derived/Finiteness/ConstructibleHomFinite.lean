/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedPoints.FinitenessCriterionAux
public import WeilConjectures.ConstructibleSheaf.FilteredColimitStabilization

/-!
# Morphisms between constructible sheaves form a finite set

Let `k` be a separably closed field, `Λ` a finite ring whose exponent is invertible in `k`, and
`X` a separated scheme of finite type over `k`. For constructible étale sheaves `F` and `G` of
`Λ`-modules on `X`, the set of morphisms `F ⟶ G` is finite
(`AlgebraicGeometry.Etale.finite_hom_of_isConstructibleSheaf`): `F` is a quotient of a finite sum
of extensions by zero `v_! Λ` along affine étale `v : V ⟶ X` (Stacks 03SA and the stabilization of
filtered unions of subsheaves of a constructible sheaf), so `F ⟶ G` injects into a finite product
of the sections `G(V)`, which are finite by the finiteness of `RΓ(V, G)`.

In particular a group acting on a constructible sheaf acts through a finite quotient.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]

/-- **Morphisms between constructible sheaves form a finite set**: over a separated scheme of
finite type over a separably closed field, with coefficients a finite ring whose exponent is
invertible. -/
theorem finite_hom_of_isConstructibleSheaf {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] : Finite (F ⟶ G) :=
  sorry

end Etale

end AlgebraicGeometry
