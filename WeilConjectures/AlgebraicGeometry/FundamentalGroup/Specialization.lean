/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import WeilConjectures.Mathlib.CategoryTheory.Galois.Prorepresentability
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.GaloisAction

/-!
# Specialization of geometric points

Let `B` be a ring which is integrally closed in a field `Ω ⊇ B`, and `a : Spec B ⟶ S` a morphism
of schemes. A point `t : Spec Ω ⟶ X` of a finite `S`-scheme `X` over `a` extends uniquely to a
point `Spec B ⟶ X` over `a` (`AlgebraicGeometry.Scheme.existsUnique_extend_of_isFinite`): over the
affine `Spec B` the scheme `X` is the spectrum of a finite `B`-algebra `A`, and a ring map
`A → Ω` over `B` lands in `B`, since the image is integral over `B`.

Restricting the extension to a point `Spec κ ⟶ Spec B` gives, for finite étale `S`-schemes, a
natural map from the fibre at `Spec Ω ⟶ Spec B ⟶ S` to the fibre at `Spec κ ⟶ Spec B ⟶ S`, the
*specialization* (`AlgebraicGeometry.Scheme.FiniteEtale.specialization`). If `Ω` and `κ` are
separably closed and `S` is connected, it is an isomorphism of fibre functors, a path from the
generic geometric point to the special one. It is compatible with automorphisms of `B` over `S`
(`AlgebraicGeometry.Scheme.FiniteEtale.specialization_hom_app_precomp`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

section Ring

variable {B A Ω : Type*} [CommRing B] [CommRing A] [CommRing Ω] [Algebra B Ω]
  [IsIntegrallyClosedIn B Ω]

end Ring

variable {S X : Scheme.{u}} {B Ω : Type u} [CommRing B] [Field Ω] [Algebra B Ω]
  [IsIntegrallyClosedIn B Ω]

namespace Scheme.FiniteEtale

variable {Y : Scheme.{u}} {κ : Type u} [IsSepClosed Ω] [Field κ] [Algebra B κ] [IsSepClosed κ]
  (a : Spec (.of B) ⟶ Y)

end Scheme.FiniteEtale

end AlgebraicGeometry
