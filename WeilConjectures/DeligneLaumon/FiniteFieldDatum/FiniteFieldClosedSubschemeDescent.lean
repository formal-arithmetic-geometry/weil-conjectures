/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Descent of closed subschemes to finite constant fields

Source: Weil conjectures blueprint, main-20261015, `sec-deligne-laumon-general`,
`sk-i-dl-general-real/lem-zl-bertini-finite-cover-curve.proof.md`, final paragraph
(blueprint: lem-zl-bertini-finite-field-descent).

The isomorphism over `Spec k` and its equation after projection to `X₀` express equality
as closed subschemes of the geometric fibre. They retain the scheme structure, including
nilpotents. The resulting automorphism of `C` is a scheme automorphism; it is semilinear
on the coefficient field and need not be a morphism over `k`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

private abbrev Stage (D : WeilConjectures.FiniteFieldDatum.{u}) :=
  {A : Subalgebra D.k₀ D.k // A.FG}

private local instance (D : WeilConjectures.FiniteFieldDatum.{u}) : Nonempty (Stage D) :=
  ⟨⟨⊥, Subalgebra.fg_bot⟩⟩

private local instance (D : WeilConjectures.FiniteFieldDatum.{u}) : IsDirectedOrder (Stage D) :=
  ⟨fun A B ↦ ⟨⟨A.1 ⊔ B.1, A.2.sup B.2⟩, show A.1 ≤ A.1 ⊔ B.1 from le_sup_left,
    show B.1 ≤ A.1 ⊔ B.1 from le_sup_right⟩⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
end WeilConjectures.FiniteFieldDatum
