/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.TwistedCoordinateSectionSign
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.SixFunctors.Etale.Derived.AdjunctionShift

/-! # Twisted coordinate-section normalization
Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: def-pur-coordinate-section-coprojection-arrows).

The supporting module spells out every arrow; this module records the normalization,
its canonical closed coprojection, its Cartier realization and its signed orientation.
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

/-- Proper projection before removing the closed coefficient unit.
Source: blueprint closed coprojection mate
(blueprint: def-pur-coordinate-section-coprojection-arrows). -/
def closedTensorProjection (W M : Etale.DerivedCategoryModule A T) :=
  Etale.ordinaryFiniteProjection A (sectionMap T) W
      ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M) ≫
    (closedImage A T).map
      (((Etale.ordinaryFiniteTensor A T).map
        ((Etale.leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
          (sectionMap T) (AffineSpace PUnit.{u + 1} T ↘ T)
          (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T)).hom.app M)).app W)

/-- The canonical closed coprojection mate, computed by inverse proper projection and
identity tensor the actual exceptional counit. Its invertibility is a conclusion.
Source: blueprint Step 8 (blueprint: def-pur-coordinate-section-coprojection-arrows). -/
def coprojectionMate (N : ℕ) (hA : (N : A) = 0)
    (M : Etale.DerivedCategoryModule A T)
    (hpf : IsIso (closedTensorProjection A T
      ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M)) :
    ((Etale.ordinaryFiniteTensor A T).obj M).obj
        ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) ⟶
      (closedImage A T).rightAdjoint.obj ((CoordinateLine.right A N hA T).obj M) := by
  letI := hpf
  exact (closedAdjunction A T).homEquiv
    (((Etale.ordinaryFiniteTensor A T).obj M).obj
      ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T))) _
    (inv (closedTensorProjection A T
      ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M) ≫
      ((Etale.ordinaryFiniteTensor A (AffineSpace PUnit.{u + 1} T)).obj
        ((Etale.ordinaryFinitePullback A (AffineSpace PUnit.{u + 1} T ↘ T)).obj M)).map
          ((closedAdjunction A T).counit.app (CoordinateLine.line A N hA T)) ≫
      eqToHom (by unfold ordinarySourceObject; rfl) ≫
      (CoordinateLine.rightCoordinates A N hA T M).hom)

/-- The positive untwisted Cartier adjunct, before tensoring; no generator is chosen.
Source: blueprint u_s (blueprint: def-pur-coordinate-section-coprojection-arrows). -/
def unitOrientation (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible) :=
  (closedAdjunction A T).homEquiv (Etale.ordinaryFiniteUnit A T) _
    (restrictedSupported A T N hN hA hT hI)

/-- The twisted adjunct is exactly u_s tensor identity, under the canonical mate.
Coefficient-first order is the symmetry-conjugate of the source's u_s tensor 1.
Source: blueprint twisted supported adjunct, Step 8
(blueprint: def-pur-coordinate-section-coprojection-arrows). -/
def CoprojectionNormalization (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible) : Prop :=
  IsIso (unitOrientation A T N hN hA hT hI) ∧
  ∀ M : Etale.DerivedCategoryModule A T, IsTateInput A T N hA M →
    ∃ (hpf : IsIso (closedProjection A T M))
      (hmate : IsIso (closedTensorProjection A T
        ((closedImage A T).rightAdjoint.obj (CoordinateLine.line A N hA T)) M)),
      IsIso (coprojectionMate A T N hA M hmate) ∧
      ordinaryOrientation A T N hN hA hT hI M hpf =
        (Etale.derivedTensorSingleUnitIso M).inv ≫
          ((Etale.ordinaryFiniteTensor A T).obj M).map
            (unitOrientation A T N hN hA hT hI) ≫
          coprojectionMate A T N hA M hmate

end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
