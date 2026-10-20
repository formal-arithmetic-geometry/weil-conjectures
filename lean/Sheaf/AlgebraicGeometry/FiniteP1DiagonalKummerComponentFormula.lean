/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineDiagonalIntegrals

/-! # The Chern-component formula for the supported diagonal boundary

Source: blueprint lem-amb-p1-diagonal-integrals, standard-chart Cartier calculation;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport


/-- The shifted-twist direct image for one of the product projections.
Source: blueprint finite diagonal check, canonical projection direct image.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[implicit_reducible]
def ordinaryFiniteP1DiagonalTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool) :
    DerivedCategoryModule A (ProjectiveLine S) :=
  (ordinaryFinitePushforward A
    (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
    (projectiveLineDiagonalProjection S a)).obj
      ((ordinaryFiniteLine A N hA
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)

/-- Apply the projected supported class to the canonical constant-object unit.
This is the canonical composite before the trace in the finite diagonal integral.
Source: blueprint finite diagonal check, supported class and composition unit.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteP1DiagonalSupportedMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) (a : Bool)
    (κ : Ext
      (C := Sheaf
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} A))
      ((lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
        (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (pullback.diagonal (ProjectiveLine S ↘ S))).obj
          (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2) :
    ordinaryFiniteUnit A (ProjectiveLine S) ⟶ ordinaryFiniteP1DiagonalTarget A N hA S a :=
  projectiveLineDiagonalAlpha A S a ≫
    (ordinaryFinitePushforward A
      (X := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) (Y := ProjectiveLine S)
      (projectiveLineDiagonalProjection S a)).map
        (X := (ordinaryFinitePushforward A (X := ProjectiveLine S)
          (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
          (pullback.diagonal (ProjectiveLine S ↘ S))).obj
            (ordinaryFiniteUnit A (ProjectiveLine S)))
        (Y := (ordinaryFiniteLine A N hA
          (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧)
        (supportedExactDerivedMap
          (lowerStar (ModuleCat.{u + 1} A) (Z := ProjectiveLine S)
            (Y := pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
            (pullback.diagonal (ProjectiveLine S ↘ S)))
          (ordinaryFiniteConstant A (ProjectiveLine S))
          (Scheme.finiteEtaleTateLine
            (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) κ)

/-- Direct-image transport from either product projection to the standard P1 projection.
This is the comparison preceding the trace in arbitraryBaseFiniteP1DiagonalTrace.
Source: blueprint lem-amb-p1-diagonal-integrals, identification of each projection.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula). -/
@[irreducible]
def ordinaryFiniteP1DiagonalChartMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) (a : Bool) :
    ordinaryFiniteP1DiagonalTarget A N hA S a ⟶
      (ordinaryFinitePushforward A
        (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).obj
          ((ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧) :=
  let e := (projectiveLineDiagonalChart S a).val
  let p := projectiveLineDiagonalProjection S a
  let L := (ordinaryFiniteLine A N hA
    (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)))⟦(2 : ℤ)⟧
  (ordinaryFinitePushforward A p).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) e.hom).unit.app L) ≫
    (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) e.hom p).hom.app
      ((ordinaryFinitePullback A e.hom).obj L) ≫
    (rightDerivedLowerStarCongr (ModuleCat.{u + 1} A)
      (projectiveLineDiagonalChart S a).property).hom.app
        ((ordinaryFinitePullback A e.hom).obj L) ≫
    (ordinaryFinitePushforward A
      (ProjectiveLine (ProjectiveLine S) ↘ ProjectiveLine S)).map
      (ordinaryFiniteShiftedLinePullback A N hA t e.hom
        ((map_natCast
          ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom N) ▸
          hS.map ((pullback.fst (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) ≫
            (ProjectiveLine S ↘ S)).appTop.hom)).hom

/-- The supported diagonal boundary has the base and relative hyperplane components.
Source: blueprint lem-amb-p1-diagonal-integrals, standard-chart proof;
lem-sp-tower-p1-arbitrary-base-integrals, steps 2 and 6.
(blueprint: lem-sp-finite-p1-diagonal-kummer-component-formula)

Proof: the diagonal's regular equations on the four product charts are y-x, x-y,
1-xy and xy-1. On the chart indexed by i,j the ideal generator is
(x0*y1-x1*y0)/(xi*yj). Its changes of basis identify the ideal dual with
p1*O(1) tensor p2*O(1), with the diagonal polynomial as its canonical section.
The given supported boundary, composed with the constant unit, is the Chern class
of this dual ideal, by ordinary_supported_kummer and uniqueness of its boundary.
Additivity of the Kummer connecting map on the Picard group gives the sum of the
two pulled-back hyperplane classes. Under the chart for projection a, one is the
relative O(1) class and the other is pulled back from the base P. Module-derived
Hom from the constant free rank-one sheaf is abelian cohomology evaluated at one:
resolve the target by injective module sheaves, forget to section-acyclic abelian
sheaves, and evaluate Hom on the constant generator. This is ordinaryFiniteClass
itself, so the Chern specification identifies the actual relative module-derived
arrow with c. Take beta to be the base O(1) class realized by that same comparison.
Taking adjuncts turns its pullback into beta followed by the twisted unit, and
turns the relative class into the stated Chern pushforward. The adjunction unit
pasting is exactly alpha; the composition and twist comparisons are exactly those
in ordinaryFiniteP1DiagonalChartMap. Thus their sum is the displayed formula.
The argument is over arbitrary rings, including the zero ring, and N=1 gives
the zero-coefficient arrows. No general derived-map detection by stalks is used. -/
theorem ordinaryFiniteP1_diagonal_kummer_component_formula (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (hPP : IsUnit (N : Γ(ProjectiveLine (ProjectiveLine S), ⊤)))
    (hW : IsUnit (N : Γ(pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S), ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine (ProjectiveLine S)) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine (ProjectiveLine S)))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA (ProjectiveLine S) hPP c)
    (hI : (pullback.diagonal (ProjectiveLine S ↘ S)).ker.IsInvertible)
    (κ : Ext
      ((lowerStar (ModuleCat.{u + 1} A) (pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant A (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N A hA) 2)
    (hκ : SupportedKummerBoundary A N hA (pullback.diagonal (ProjectiveLine S ↘ S))
      hI hW κ) :
    ∀ a : Bool, ∃ β : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
              (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
            ordinaryFiniteP1DiagonalSupportedMap A N hA S a κ ≫
              ordinaryFiniteP1DiagonalChartMap A N hA t S hS a =
            β ≫ ordinaryFiniteP1Unit A N hA t (ProjectiveLine S) hP +
              ordinaryFiniteP1ChernPushforward A N hA (ProjectiveLine S) c := by
  sorry

end AlgebraicGeometry.Etale
