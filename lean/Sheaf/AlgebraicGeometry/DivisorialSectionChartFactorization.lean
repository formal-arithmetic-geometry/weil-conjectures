/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.LogRegularPair
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Simultaneous factorization of divisorial sections in an fs chart

Source: Illusie--Laszlo--Orgogozo, Exposé VI §§1.1, 1.4 (printed p. 69),
and Proposition 1.9 proof (printed p. 71)
(blueprint: lem-trf-divisorial-section-chart-factorization).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A finite list of divisorial sections factors simultaneously as units times chart elements
on one pointed étale neighbourhood; the list may be empty. The chart condition is imposed
at every geometric point of that neighbourhood using the prescribed divisorial stalks.

Source: ILO, Exposé VI §§1.1, 1.4 and Proposition 1.9 proof, printed pp. 69, 71
(blueprint: lem-trf-divisorial-section-chart-factorization).

Proof:
1. Each `h i` lies in the divisorial sections by its invertibility on the complement
   (`def-trf-log-regular-pair`).
2. Choose an fs chart on an étale cover of Y. Pull it back to V using
   `lem-weil-pbc-etale-covering-base-change`, and lift the prescribed geometric point
   with the same field by `lem-weil-pbc-etale-cover-geometric-point-lift`.
   Composition and cancellation of étale maps are
   `lem-weil-pbc-etale-composition-cancellation`. The restriction-stalk identification
   of `lem-trf-finite-monoid-stalk-data-spreading` preserves the chart pushout condition.
3. In the stalk pushout every element is represented by a pair consisting of a monoid
   element and a ring unit: the coproduct of commutative monoids is their product,
   and the pushout quotients it by the unit-identification relations. Thus the germ
   of each `h i` is a unit times the image of some `a i`.
4. Apply the finite-elements part of `lem-trf-finite-monoid-stalk-data-spreading` to
   these units and their inverses. Its finite-equalities part gives a further common
   pointed refinement on which both the inverse and factorization equations hold.
   Restrict the chart there; restriction stalks preserve its pushout condition.
   The resulting maps are étale by composition and cancellation, and retain the
   original geometric-point field. For the empty list retain the chart neighbourhood
   from step 2 and omit all spreading applications.
-/
theorem exists_divisorial_section_chart_factorization
    {Y U : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    [IsLocallyNoetherian Y] (hU : DenseRange j)
    (hlog : IsDivisorialFineSaturatedLogRegularPair Y U j hU)
    {V : Scheme.{u}} (f : V ⟶ Y) [Etale f]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ V)
    (r : ℕ) (h : Fin r → Γ(V, ⊤))
    (hh : ∀ i : Fin r, IsUnit ((pullback.fst f j).appTop (h i))) :
    ∃ (W : Y.Etale) (g : W.left ⟶ V) (w : Spec (.of Ω) ⟶ W.left),
      Etale g ∧ g ≫ f = W.hom ∧ w ≫ g = y ∧
      ∃ hunit : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
          (t : Spec (.of Ω') ⟶ Y),
          IsUnit.submonoid (strictLocalRing Y t) ≤ divisorialStalk j t,
        ∃ (P : Type u) (_ : CommMonoid P) (c : P →* divisorialSections j W),
          IsFineSaturatedMonoid P ∧
          (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
            (t : Spec (.of Ω') ⟶ Y) (z : (Scheme.pointSmallEtale t).fiber.obj W),
            IsDivisorialStalkChart (divisorialStalk j t) (hunit Ω' t)
              ((divisorialGerm j t W z).comp c)) ∧
          ∃ (a : Fin r → P) (ε : Fin r → Γ(W.left, ⊤)ˣ),
            ∀ i : Fin r, g.appTop (h i) = (ε i).val * (c (a i)).val := by
  sorry

end AlgebraicGeometry
