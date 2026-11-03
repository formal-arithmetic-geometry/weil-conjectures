/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateSectionNormalization.TwistedCoordinateSectionCore

/-! # Twisted coordinate-section Kummer normalization

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: def-pur-coordinate-section-ordinary-arrows).

The helpers below are the canonical arrows in this normalization statement. In particular,
composition is identified with the identity by conjugating the normalized compact-support
comparison, and the affine comparison is the existing integration transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
open AffineLinePurity VectorIntegrationSite

variable (A : Type (u + 1)) [CommRing A] [Finite A] (T : Scheme.{u})

/-- Coefficient-first proper projection, followed by s*p*=id and the coefficient unitor.
Its inverse is the closed supported source identification, rather than a chosen map.
Source: blueprint twisted supported adjoint
(blueprint: def-pur-coordinate-section-ordinary-arrows). -/
def closedProjection (M : Etale.DerivedCategoryModule A T) :=
  Etale.ordinaryFiniteProjection A (sectionMap T) (Etale.ordinaryFiniteUnit A T)
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
    (closedImage A T).map
      (((Etale.ordinaryFiniteTensor A T).map
        ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
          (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)).hom.app M)).app _ ≫
        (Etale.derivedTensorSingleUnitIso M).hom)

/-- The canonical tensor of the supported Cartier morphism, with proper projection inverted.
The parameter is the inverse of a specified arrow, so no orientation is chosen here.
Source: blueprint c_s tensor 1, with precisely its two tensor symmetries
(blueprint: def-pur-coordinate-section-ordinary-arrows). -/
def tensorSupported (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :
    (closedImage A T).obj M ⟶ (CoordinateLine.right A N hA T).obj M := by
  letI := hpf
  unfold CoordinateLine.right Etale.ordinaryFiniteTwistedPullback
  exact inv (closedProjection A T M) ≫
    ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
      (restrictedSupported A T N hN hA hT hI)

/-- Exceptional adjunct of the canonical twisted supported arrow.
Source: blueprint u_(s,M) (blueprint: def-pur-coordinate-section-ordinary-arrows). -/
def ordinaryOrientation (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible)
    (M : Etale.DerivedCategoryModule A T) (hpf : IsIso (closedProjection A T M)) :=
  (closedAdjunction A T).homEquiv M _ (tensorSupported A T N hN hA hT hI M hpf)

/-- All ordinary equalities, retaining the supported arrow, the open counit and the
identity-normalized source. The second equation is the tensor transpose; the last
is its exceptional transpose under the two actual adjunctions.
Source: blueprint Steps 3, 6, 8--9
(blueprint: def-pur-coordinate-section-ordinary-arrows). -/
def OrdinaryNormalization (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
    (Etale.ordinaryFinitePushforward A (ProjectiveLine T ↘ T)).map
      ((Etale.affineTraceOpenAdjunction A T).counit.app
        ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine T))⟦(2 : ℤ)⟧)) =
      Etale.ordinaryFiniteP1ChernPushforward A N hA T
        (Etale.projectiveLineTraceDatum N hN A hA T hT).chern) ∧
  ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT =
    Etale.ordinaryFiniteP1ChernPushforward A N hA T
        (Etale.projectiveLineTraceDatum N hN A hA T hT).chern ≫
      Etale.ordinaryFiniteProjectiveLineTrace N hN A hA T hT) ∧
  ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
    (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
      CoordinateLine.integration A N hA T hN hT = 𝟙 _) ∧
  ∀ r : ℕ, ∃ hpf : IsIso (closedProjection A T
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)),
    IsIso (ordinaryOrientation A T N hN hA hT hI
      (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ∧
    ((sectionComposition A T).inv.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) ≫
      (compact A T).map (tensorSupported A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf) ≫
      (CoordinateLine.adjunction A N hA T hN hT).counit.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) =
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).inv ≫
      ((Etale.ordinaryFiniteTensor A T).obj
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).map
          ((sectionComposition A T).inv.app (Etale.ordinaryFiniteUnit A T) ≫
            (compact A T).map (restrictedSupported A T N hN hA hT hI) ≫
            CoordinateLine.integration A N hA T hN hT) ≫
      (Etale.derivedTensorSingleUnitIso
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)).hom) ∧
    (ordinaryOrientation A T N hN hA hT hI
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) hpf ≫
      (closedImage A T).rightAdjoint.map
        ((CoordinateLine.comparison A N hA T hN hT).hom.app
          (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r)) ≫
      (exceptionalComposition A T).hom.app
        (Etale.SectionLocalDualizingComparisons.tateObject A N hA T r) = 𝟙 _)

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
