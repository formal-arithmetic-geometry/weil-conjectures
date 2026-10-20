/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G5
-/
module

public import Sheaf.AlgebraicGeometry.ProjectiveLineTrace

/-! # Naturality of the hyperplane Kummer class

Source: blueprint main-20261015, thm-amb-p1-decomposition, arbitrary-base compatibility;
the universal-base argument of lem-sp-tower-p1-arbitrary-base-integrals, steps 1–4.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  projectiveLineTraceTransport projectiveLineTraceDatum

/-- The ordered source of the finite P1 decomposition, constructed as a biproduct.
Source: blueprint thm-amb-p1-decomposition, after twisting by A(1)[2].
(blueprint: lem-sp-finite-p1-kummer-naturality). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingSource (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFiniteLine A N hA S)⟦(2 : ℤ)⟧ ⊞ ordinaryFiniteUnit A S

/-- The target of the finite P1 decomposition, constructed by derived direct image.
Source: blueprint thm-amb-p1-decomposition, after twisting by A(1)[2].
(blueprint: lem-sp-finite-p1-kummer-naturality). -/
@[implicit_reducible]
def ordinaryFiniteP1SplittingTarget (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (S : Scheme.{u}) : DerivedCategoryModule A S :=
  (ordinaryFinitePushforward A (X := ProjectiveLine S) (Y := S)
    (ProjectiveLine S ↘ S)).obj
      ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The two specified components, before asserting invertibility.
Source: blueprint thm-amb-p1-decomposition, after twisting by A(1)[2].
(blueprint: lem-sp-finite-p1-kummer-naturality). -/
@[irreducible]
def ordinaryFiniteP1SplittingMap (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    ordinaryFiniteP1SplittingSource A N hA S ⟶ ordinaryFiniteP1SplittingTarget A N hA S :=
  biprod.desc (ordinaryFiniteP1Unit A N hA t S hS)
    (ordinaryFiniteP1ChernPushforward A N hA S c)

/-- The hyperplane Kummer class and its two-component map are natural over every base.
Over a Noetherian base this is the already normalized Chern morphism.
Source: blueprint thm-amb-p1-decomposition, arbitrary-base compatibility, and
lem-sp-tower-p1-arbitrary-base-integrals, steps 2–3.
(blueprint: lem-sp-finite-p1-kummer-naturality)

Proof: the hyperplane equation is t on the first standard chart and the unit ideal
on the other. It is Cartier after every change of base, and its dual ideal has the
O(1) transition function. The supported Kummer class, composed with the constant
unit, has the prescribed abelian Kummer image. Module-derived Hom from the constant
free rank-one sheaf is naturally abelian cohomology after forgetting coefficients
and evaluating at one. Indeed resolve the target by injective module sheaves; Hom
from the constant free module is sections degreewise, and forgetting an injective
module gives a global-sections-acyclic abelian sheaf. Evaluation on the integral
generator one identifies the comparison with ordinaryFiniteClass itself. Thus this
image determines the module-derived arrow c, not just an arbitrary isomorphism of
cohomology groups. The kernel inclusion of roots is monic, so the root normalization
determines its pullback comparison uniquely; the pure-tensor generators determine
the line comparison uniquely. Hence the normalized transport in the supported
Kummer theorem agrees with the fixed projectiveLineTraceTransport.
The supported Kummer pullback equation and the mate unit identity identify its
pullback with the corresponding arrow over the new base. This proves both the
Chern specification and agreement with the normalized Noetherian datum. Taking
adjoints gives naturality of the Chern direct-image component. The exchange mate
formula and adjunction triangles give naturality of the twisted unit component.
The biproduct universal property combines these two equations into the displayed
square. All chart equations remain valid over the zero ring; when N=1 the same
cohomology construction gives the unique zero-coefficient arrows. -/
theorem exists_ordinaryFiniteP1KummerNaturality (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0) :
    ∃ c : ∀ (S : Scheme.{u}) (_hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteUnit A (ProjectiveLine S) ⟶
          (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧,
      (∀ (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))),
        ordinaryFiniteP1ChernSpec A N hA S
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom) (c S hS) ∧
        (∀ [IsNoetherian S],
          c S hS = (projectiveLineTraceDatum N hN A hA S hS).chern)) ∧
      ∀ {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
          (hS' : IsUnit (N : Γ(S', ⊤))),
        (ordinaryFinitePullback A (X := S') (Y := S) f).map (ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S hS (c S hS)) ≫
          ordinaryFiniteP1Exchange A f
            ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
          (ordinaryFinitePushforward A (X := ProjectiveLine S') (Y := S')
            (ProjectiveLine S' ↘ S')).map
            (ordinaryFiniteShiftedLinePullback A N hA
              (projectiveLineTraceTransport N hN A hA)
              (X := ProjectiveLine S') (Y := ProjectiveLine S)
              (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
              ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
                hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
        ordinaryFiniteP1DecompositionSourceMap A N hA
            (projectiveLineTraceTransport N hN A hA) f hS ≫
          ordinaryFiniteP1SplittingMap A N hA
            (projectiveLineTraceTransport N hN A hA) S' hS' (c S' hS') := by
  sorry


end AlgebraicGeometry.Etale
