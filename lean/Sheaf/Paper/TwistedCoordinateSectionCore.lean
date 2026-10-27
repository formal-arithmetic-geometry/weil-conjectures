/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q21
-/
module

public import Sheaf.Paper.CoordinateLineAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import Sheaf.Paper.AffineLinePurityComparison
public import Sheaf.AlgebraicGeometry.OrdinarySupportedCartierKummer
public import Sheaf.Paper.PurityAffineLineOrientation
public import Sheaf.AlgebraicGeometry.EtaleClosedAmbientAdjoint
public import Sheaf.Paper.ClosedSectionCompactOrigin
public import Sheaf.Paper.ClosedFiniteAdjointCounitTransport
public import Sheaf.Paper.PurityCoprojection
public import Sheaf.AlgebraicGeometry.PurityRelativeCone
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import Sheaf.Paper.SectionLocalComparisonData
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
import Sheaf.Paper.LineZeroGeometry
import Sheaf.AlgebraicGeometry.PrincipalTorsorYonedaSign
import Sheaf.SixFunctors.EtaleOpenTensor
import Sheaf.SixFunctors.CompositionProjectionMate
import Sheaf.Paper.CompactSupportSiteCoherence
import Sheaf.AlgebraicGeometry.OrdinaryDerivedOpenClosedAdjunctions
import WeilConjectures.SixFunctors.OpenClosed.Exact

/-! # Twisted coordinate-section Kummer normalization

Source: current blueprint, sec-smooth-purity/sk-prop-an,
cor-pur-affine-space-zero-section-purity.proof.md, rank-one and even-shift paragraphs
(blueprint: def-pur-coordinate-section-core-arrows).

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

/-- The actual closed zero section in the integration chart.
Source: blueprint rank-one coordinate (blueprint: def-pur-coordinate-section-core-arrows).
-/
abbrev sectionMap := AffineSpace.zeroSection PUnit.{u + 1} T

/-- Closed direct image in the ordinary derived category.
Source: blueprint supported Kummer map (blueprint:
lem-pur-twisted-coordinate-section-normalization).
-/
abbrev closedImage := Etale.ordinaryFinitePushforward A (sectionMap T)

/-- Compact support at the specified projective-line compactification.
Source: blueprint trace restriction (blueprint: def-pur-coordinate-section-core-arrows).
-/
abbrev compact := Etale.rightDerivedLowerShriekOfCompactification
  (ModuleCat.{u + 1} A) (affineTraceLineCompactification T)

/-- The recorded closed-image left-adjoint structure, exposed for these coordinates.
Source: blueprint closed adjunction (blueprint: def-pur-coordinate-section-core-arrows).
-/
instance closedLeftAdjoint : (closedImage A T).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerStar_of_isClosedImmersion A (sectionMap T)

/-- The recorded compact-support left-adjoint structure at the literal chart.
Source: blueprint ordinary adjunction (blueprint: def-pur-coordinate-section-core-arrows).
-/
instance compactLeftAdjoint : (compact A T).IsLeftAdjoint :=
  Etale.isLeftAdjoint_rightDerivedLowerShriekOfCompactification A
    (affineTraceLineCompactification T)

/-- Identity-normalized closed-section compact-support composition on ordinary complexes.
Source: Stacks 0F7J, 0F7K; blueprint ps=id
(blueprint: def-pur-coordinate-section-core-arrows). -/
def sectionComposition : closedImage A T ⋙ compact A T ≅ 𝟭 (Etale.DerivedCategoryModule A T) :=
  letI : HasCompactification (AffineSpace PUnit.{u + 1} T ↘ T) :=
    (affineTraceLineCompactification T).hasCompactification
  letI : HasCompactification (sectionMap T ≫ (AffineSpace PUnit.{u + 1} T ↘ T)) :=
    HasCompactification.of_eq (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T).symm
  Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar
        (ModuleCat.{u + 1} A) (sectionMap T)).symm _ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.rightDerivedLowerShriekIso A (affineTraceLineCompactification T)) ≪≫
    Etale.unboundedEtaleLowerShriekCompIso A (sectionMap T)
      (AffineSpace PUnit.{u + 1} T ↘ T) ≪≫
    Etale.unboundedEtaleLowerShriekCongr A
      (AffineSpace.zeroSection_comp_over PUnit.{u + 1} T) ≪≫
    Etale.unboundedEtaleLowerShriekId A T

/-- The closed-support adjunction is the existing ordinary closed direct-image adjunction.
Source: blueprint exceptional adjunct (blueprint: def-pur-coordinate-section-core-arrows).
-/
def closedAdjunction : closedImage A T ⊣ (closedImage A T).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint (closedImage A T)

/-- The ordinary compact-support adjunction at the actual projective chart.
Source: blueprint integration transpose (blueprint:
lem-pur-twisted-coordinate-section-normalization).
-/
def compactAdjunction : compact A T ⊣ (compact A T).rightAdjoint :=
  Adjunction.ofIsLeftAdjoint (compact A T)

/-- Composition of exceptional functors with ps=id, preserving the actual two adjunctions.
Source: blueprint composition comparison; Mathlib conjugateIsoEquiv
(blueprint: def-pur-coordinate-section-core-arrows). -/
def exceptionalComposition :
    (compact A T).rightAdjoint ⋙ (closedImage A T).rightAdjoint ≅
      𝟭 (Etale.DerivedCategoryModule A T) :=
  conjugateIsoEquiv ((closedAdjunction A T).comp (compactAdjunction A T))
    Adjunction.id (sectionComposition A T).symm

/-- Ordinary supported Cartier class, selected from its unique relative-boundary normalization.
Source: Stacks 03PL, 0A45; blueprint Cartier map
(blueprint: def-pur-coordinate-section-core-arrows). -/
def ordinaryClass (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible) :=
  (Etale.ordinary_supported_kummer_uniqueBoundary _ N hN A hA hT
    (sectionMap T) hI).exists.choose

/-- The derived ordinary supported morphism c_s, with the canonical exact-image identification.
Source: blueprint c^e_s (blueprint: def-pur-coordinate-section-core-arrows). -/
def ordinarySupported (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(AffineSpace PUnit.{u + 1} T, ⊤)))
    (hI : (sectionMap T).ker.IsInvertible) :
    (closedImage A T).obj (Etale.ordinaryFiniteUnit A T) ⟶
      (Etale.ordinaryFiniteLine A N hA (AffineSpace PUnit.{u + 1} T))⟦(2 : ℤ)⟧ :=
  Etale.supportedExactDerivedMap (Etale.lowerStar (ModuleCat.{u + 1} A) (sectionMap T))
    (Etale.ordinaryFiniteConstant A T)
    (Scheme.finiteEtaleTateLine _ N A hA) (ordinaryClass A T N hN hA hT hI)

/-- The ordinary supported arrow in the exact chart-restriction coordinates of gamma.
Source: blueprint finite etale-origin comparison
(blueprint: def-pur-coordinate-section-core-arrows). -/
def restrictedSupported (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (hT : IsUnit (N : Γ(T, ⊤))) (hI : (sectionMap T).ker.IsInvertible) :=
  ordinarySupported A T N hN hA (affineTraceInvertible N T hT 1) hI ≫
    (Etale.ordinaryFiniteShiftedLinePullback A N hA
      (Etale.projectiveLineTraceTransport N hN A hA) (ProjectiveLine.affineChart T)
      (affineTraceProjectiveInvertible N T hT)).inv


end AlgebraicGeometry.ProEtale.CoordinateSectionNormalization
