/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A7
-/
module

public import Sheaf.AlgebraicGeometry.OrdinarySupportedKummerSystem
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# The two components of the Chern adjunct of the projective-line diagonal

Source: blueprint main-20261015, lem-amb-p1-diagonal-integrals, diagonal equation;
blueprint def-amb-p1-trace, the two components of the projective-line splitting.
(blueprint: lem-amb-p1-diagonal-chern-adjunct).

The class calculation is before composition with the trace. It specifies both
components, including the base Chern class which the trace subsequently kills.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Canonical transport of the shifted finite line's direct image along a projective-line
chart. This is the prefix of the transported projective-line trace, before its trace factor.
Source: blueprint lem-amb-p1-diagonal-integrals, proof step 1
(blueprint: lem-amb-p1-diagonal-chern-adjunct). -/
@[irreducible]
def ordinaryFiniteShiftedLineChart (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (p : pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⟶ ProjectiveLine S)
    (e : ProjectiveLine (ProjectiveLine S) ≅
      pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
    (he : e.hom ≫ p = (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)) :
    (ordinaryFinitePushforward A p).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧) ⟶
    (ordinaryFinitePushforward A (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let r := ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
      (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A) he).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
      (ordinaryFinitePushforward A r).map
        (ordinaryFiniteShiftedLinePullback A N hA
          t e.hom (by
            simpa using hS.map
              ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
                (ProjectiveLine S ↘ S)).appTop.hom)).hom

/-- The diagonal's Chern class has components `(c1(O(1)), 1)` over either projection.
The comparison is the same canonical chart comparison used to transport the trace.
This statement concerns the ordinary Chern class before integration, and uses no trace.

Source: blueprint main-20261015, lem-amb-p1-diagonal-integrals, equation
`x0*y1-x1*y0`; def-amb-p1-trace, normalized two-summand decomposition.
(blueprint: lem-amb-p1-diagonal-chern-adjunct).

Proof:
On the four product charts, divide x0*y1-x1*y0 by the product of the two
nonvanishing homogeneous coordinates. These are the local generators of the diagonal
ideal. Their dual generators transform by the products of the O(1) transition units
on the two factors. Consequently O(Delta) is p1^*O(1) tensor p2^*O(1). This holds over
any base, including the empty and nonreduced bases; no choice of a point is involved.
Under e, one factor is the relative O(1) of P1 over P and the other is r^*O_P(1).
The Kummer boundary is additive on tensor products and natural for pullback. Its scalar
extension to A has the same properties. The scalar-Chern hypothesis and the two
prescribed projective-line Chern specifications thus identify the pullback of c
with the sum of the relative Chern class and the pullback of the base Chern class.
The theorem `kummerFirstChernRealization_bijective` in
`Sheaf.Paper.KummerAdditivity` identifies the actual forget-and-evaluate-on-one
comparison with ordinaryFiniteClass and makes it injective. Thus the scalar equality
gives equality of the ordinary module-derived Chern arrows. Equivalently, the scalar
specification identifies each supplied Chern arrow with `kummerFirstChern`, by
unfolding that definition and applying `Equiv.eq_symm_apply` to the specified
bijective realization. Additivity uses `Pic.toCohomologicalPicardGroup_mul` and
`map_add` for the Kummer boundary and the root coefficient map. Pullback uses
`rootsOfUnityCohomologyMap_kummerδ₁` and
`gmCohomologyMap_toCohomologicalPicardGroup`, with the root and pure-tensor
normalizations in t fixing the coefficient comparisons.
Take inverse-image/direct-image adjuncts. Naturality of the adjunction unit
makes the pulled-back base class the base Chern arrow followed by the twisted unit;
the relative class becomes the stated Chern pushforward. The canonical direct-image
composition comparison respects these adjuncts, giving exactly the displayed chart
transport. The two coordinate alternatives just exchange the tensor factors; the
positive degree-two classes introduce no sign. -/
theorem projectiveLine_diagonal_chern_adjunct (N : ℕ)
    (A : Type (u + 1)) [CommRing A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (cS : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (cP : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hcS : ordinaryFiniteP1ChernSpec A N hA S
      (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) cS)
    (hcP : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S)
      (by
        simpa using hS.map
          ((ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S) ≫
            (ProjectiveLine S ↘ S)).appTop.hom) cP)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (c : ordinaryFiniteUnit A
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ⟶
      (ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteClass A
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (Scheme.finiteEtaleTateLine
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2 c =
      supportedKummerChern A N hA (pullback.diagonal (ProjectiveLine S ↘ S)) hI
        (by
          simpa only [map_natCast] using hS.map
            ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
              (ProjectiveLine S ↘ S)).appTop.hom))
    (p : pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ⟶ ProjectiveLine S)
    (e : ProjectiveLine (ProjectiveLine S) ≅
      pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
    (he : e.hom ≫ p = (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S))
    (hcoords :
      (p = pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ∧
        e.hom ≫ pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) =
        ProjectiveSpace.map (ULift (Fin 2)) (ProjectiveLine S ↘ S)) ∨
      (p = pullback.snd (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) ∧
        e.hom ≫ pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S) =
        ProjectiveSpace.map (ULift (Fin 2)) (ProjectiveLine S ↘ S))) :
    supportedDerivedUnit A p ≫ (ordinaryFinitePushforward A p).map c ≫
      ordinaryFiniteShiftedLineChart N A hA t S hS p e he =
      cS ≫ ordinaryFiniteP1Unit A N hA t (ProjectiveLine S)
        (by simpa using hS.map (ProjectiveLine S ↘ S).appTop.hom) +
      ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) cP := by
  sorry

end AlgebraicGeometry.Etale
