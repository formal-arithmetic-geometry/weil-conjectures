/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q137
-/
module

public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Artinian.Defs

/-! # Versality of a proper algebraic-space curve family

Source: Stacks Project, artin.tex, definition-versal, and Formal Deformation Theory,
definition-smooth-morphism (blueprint: def-sfb-proper-curve-versality).

Cartesian squares retain the specified isomorphisms to base changes. The final equality
requires the lift to extend the given isomorphism, rather than just its isomorphism class.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProperCurveFamily

/-- The Artinian local lifting condition for versality at a point. The surjective residue
map `r` identifies the residue field of `A` with the actual residue field of `u`; its
composite with the surjection `q` gives the same identification for `A'`. Thus no
coefficient-field embedding in either Artinian ring is assumed. A cartesian map from
`Z` to `x` specifies the isomorphism of the reduction of `Y` with the family pulled
back along `a`. The lifted cartesian map must restrict to this very map.
Source: Stacks Project, artin.tex, definition-versal, equation-hat-x, and Formal
Deformation Theory, definition-smooth-morphism
(blueprint: def-sfb-proper-curve-versality). -/
def IsVersalAt {S : Scheme.{u}} {T : Over S} (x : ProperCurveFamily T) (u₀ : T.left) :
    Prop :=
  ∀ (A' A : CommRingCat.{u}) [IsArtinianRing A'] [IsLocalRing A']
    [IsArtinianRing A] [IsLocalRing A] (q : A' ⟶ A),
    Function.Surjective q.hom → IsNilpotent (RingHom.ker q.hom) →
    ∀ (r : A ⟶ T.left.residueField u₀), Function.Surjective r.hom →
    ∀ (s' : Spec A' ⟶ S)
      (a : Over.mk (Spec.map q ≫ s') ⟶ T),
      Spec.map r ≫ a.left = T.left.fromSpecResidueField u₀ →
    ∀ (Y : ProperCurveFamily (Over.mk s'))
      (Z : ProperCurveFamily (Over.mk (Spec.map q ≫ s')))
      (j : Z.space.obj.obj ⟶ Y.space.obj.obj)
      (z : Z.space.obj.obj ⟶ x.space.obj.obj),
      IsPullback j Z.projection Y.projection
        (yoneda.map (Over.homMk (Spec.map q) rfl)) →
      IsPullback z Z.projection x.projection (yoneda.map a) →
      ∃ (b : Over.mk s' ⟶ T) (w : Y.space.obj.obj ⟶ x.space.obj.obj),
        Spec.map q ≫ b.left = a.left ∧
        IsPullback w Y.projection x.projection (yoneda.map b) ∧ j ≫ w = z

end AlgebraicGeometry.ProperCurveFamily
