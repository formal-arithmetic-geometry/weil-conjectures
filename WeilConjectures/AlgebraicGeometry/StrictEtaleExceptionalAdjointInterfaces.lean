/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictEtaleSystemInterfaces
public import WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjoint

/-! # Strict etale exceptional-adjoint interfaces

Source: Zheng Constructions 4.1 and 5.15, Lemma 5.22 and Proposition 2.29(2)
(blueprint: def-sf-strict-etale-exceptional-adjoint-interfaces).

The record fixes the derived adjoint, evaluated units/counits and quotient mates.
Its constructions are the published declarations of
`WeilConjectures.AlgebraicGeometry.EtaleCoefficientSystemAdjoint`, reexported here unchanged:
`StrictEtaleExceptionalAdjointData` (an additive, shift-commuting right adjoint of the strict
compact-support functor, its finite-level adjunctions, evaluation isomorphisms and quotient
comparisons), `StrictEtaleExceptionalAdjointCoherence` (exactness, linearity, the counit
mate equation, open/proper quotient mates, quotient identity/composition and transition
equations, a uniform lower bound and preservation of bounded-below normalized systems),
the subtype `StrictEtaleExceptionalAdjoint` and its accessors `right`, `adjunction`,
`levelRight`, `levelAdjunction`, `evaluation` and `quotientComparison`.
They are not redeclared, so that one definition per notion is kept.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The strict etale exceptional-adjoint interface of this node under its descriptive name:
the transparent name of the published `StrictEtaleExceptionalAdjoint`, the data of
`StrictEtaleExceptionalAdjointData` subject to `StrictEtaleExceptionalAdjointCoherence`.
Source: Zheng, Lemmas 5.16 and 5.22, Proposition 5.24 and Proposition 2.29(2)
(blueprint: def-sf-strict-etale-exceptional-adjoint-interfaces). -/
abbrev StrictEtaleExceptionalAdjointInterface (O : Type (u + 1)) [CommRing O] (ell : O)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (S : StrictEtaleCompactSupport O ell c) :=
  StrictEtaleExceptionalAdjoint O ell c S

end AlgebraicGeometry
