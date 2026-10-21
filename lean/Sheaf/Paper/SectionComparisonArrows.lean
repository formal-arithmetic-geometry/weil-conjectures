/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q72
-/
module

public import Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence

/-! # Canonical section-specialization arrows without the global purity proof graph

Source: sk-thm-dnc, opening paragraph and correction at one
(blueprint: def-pur-noetherian-section-specialization-arrows).

This interface contains the seven plain arrow constructions on ordinary unbounded
categories. It does not import the global specialization theorem or integral coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.SectionComparisonArrows

/-- The actual ordinary etale family on the extended-Rees deformation.
Source: sk-thm-dnc, opening paragraph
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def family (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) (s : S ⟶ V) [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    DerivedCategoryModule A (AffineSpace (ULift.{u} (Fin 1)) S) :=
  sectionInvariant A (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection

/-- Pull the canonical exceptional base-change mate to compatible sections. This is a map,
not an arbitrarily chosen isomorphism. Source: sk-thm-dnc, fibre identifications;
prop-asd-smooth-base-change (blueprint: def-pur-noetherian-section-specialization-arrows). -/
def sectionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (f' : X' ⟶ Y') [HasCompactification f'] [QuasiCompact f']
    (b : Y' ⟶ Y) (v : X' ⟶ X) (sq : IsPullback v f' f b)
    (s : Y ⟶ X) (s' : Y' ⟶ X') (hs : s' ≫ v = b ≫ s) :
    (upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj
      (sectionInvariant A f s) ⟶ sectionInvariant A f' s' :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) b s).app _).inv ≫
    ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) s' v (b ≫ s) hs.symm).app _).hom ≫
      (upperStar (ModuleCat.{u + 1} A) s').leftDerivedFunctor.map
        (dualizingComplexBaseChangeMap A sq)

/-- The specified fibre map at t=1. Source: sk-thm-dnc, opening fibre comparison
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def atOne (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        (family A g s) ⟶ sectionInvariant A g s :=
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) g
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
    (Scheme.Hom.deformationSpaceOneFibre g s)
    (Scheme.Hom.isPullback_deformationSpaceOneFibre g s)
    s.deformationSpaceSection s (Scheme.Hom.comp_deformationSpaceOneFibre hs)

/-- The specified fibre map at t=0 to the actual normal cone.
Source: sk-thm-dnc, opening fibre comparison
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def atZero (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) (s : S ⟶ V) [IsClosedImmersion s]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)] :
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.obj
        (family A g s) ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  sectionMap A (Scheme.Hom.deformationSpaceProj g s) (Scheme.Hom.normalConeProj g s)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S) s.ker.normalConeToDeformationSpace
    (Scheme.Hom.isPullback_normalConeToDeformationSpace g s)
    s.deformationSpaceSection s.normalConeZeroSection
    Scheme.Hom.normalConeZeroSection_comp_normalConeToDeformationSpace

/-- Normalization at t=1, with the identity on the source section complex expressed using
its canonical fibre identification. Source: sk-thm-dnc, normalization
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def Normalized (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] [QuasiCompact g]
    (s : S ⟶ V) [IsClosedImmersion s] (hs : s ≫ g = 𝟙 S)
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) : Prop :=
  (upperStar (ModuleCat.{u + 1} A)
    (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.hom ≫
      (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
        (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
        (AffineSpace.oneSection_comp_over (ULift.{u} (Fin 1)) S)).hom.app _ =
    atOne A g s hs

/-- Specialization at zero, read through the canonical zero-fibre mate. When that mate
is invertible, this is the isomorphism denoted delta in the node. Its formula is the
inverse of the zero restriction of kappa, with both canonical fibre identifications.
Source: sk-thm-dnc, final specialization
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def specialization (A : Type (u + 1)) [CommRing A] [Finite A] {V S : Scheme.{u}}
    (g : V ⟶ S) [HasCompactification g] (s : S ⟶ V) [IsClosedImmersion s]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.normalConeProj g s)]
    [QuasiCompact (Scheme.Hom.normalConeProj g s)]
    (κ : family A g s ≅
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj
          (sectionInvariant A g s)) :
    sectionInvariant A g s ⟶
      sectionInvariant A (Scheme.Hom.normalConeProj g s) s.normalConeZeroSection :=
  (leftDerivedUpperStarCompSectionIso (ModuleCat.{u + 1} A)
    (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)
    (AffineSpace.zeroSection_comp_over (ULift.{u} (Fin 1)) S)).inv.app _ ≫
      (upperStar (ModuleCat.{u + 1} A)
        (AffineSpace.zeroSection (ULift.{u} (Fin 1)) S)).leftDerivedFunctor.map κ.inv ≫
          atZero A g s

/-- The canonical comparison between pullback from S and pullback from S' on affine lines.
Source: sk-thm-dnc, base-change formula for kappa
(blueprint: def-pur-noetherian-section-specialization-arrows). -/
def linePullback (A : Type (u + 1)) [CommRing A] {S S' : Scheme.{u}}
    (b : S' ⟶ S) (C : DerivedCategoryModule A S) :
    (upperStar (ModuleCat.{u + 1} A) (AffineSpace.map (ULift.{u} (Fin 1)) b)).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A)
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).leftDerivedFunctor.obj C) ≅
    (upperStar (ModuleCat.{u + 1} A)
      (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S')).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} A) b).leftDerivedFunctor.obj C) :=
  ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (AffineSpace.map (ULift.{u} (Fin 1)) b)
    (AffineSpace (ULift.{u} (Fin 1)) S ↘ S)).app C).symm ≪≫
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin 1)) S' ↘ S') b
        (AffineSpace.map (ULift.{u} (Fin 1)) b ≫
          (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (AffineSpace.map_over (n := ULift.{u} (Fin 1)) b)).app C

end AlgebraicGeometry.Etale.SectionComparisonArrows
