/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackCoherence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Canonical compactification mates under an isomorphic Cartesian realization

Source: latest blueprint, sec-six-functors-basics/sk-thm-sf-comp-composition/
det-sf-comp-composition-base-change.proof.md,
Clauses (1) and (3).
(blueprint: lem-pod-condensed-compactification-square-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
attribute [local irreducible] HasDerivedCategory.standard
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory DerivedCategory.monoidalClosed

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The dependency internal-module category, with its existing coefficient ring.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)

/-- The ordinary unbounded derived category of the dependency module category.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodDerived (T : Scheme.{u}) := DerivedCategory (PodModules Λ T)

/-- The recorded total left derived module pullback.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodPullback {A B : Scheme.{u}} (a : A ⟶ B) :
    PodDerived Λ B ⥤ PodDerived Λ A := moduleObjectDerivedPullback Λ a

/-- The recorded total right derived module direct image.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodPushforward {A B : Scheme.{u}} (a : A ⟶ B) :
    PodDerived Λ A ⥤ PodDerived Λ B := moduleObjectDerivedPushforward Λ a

/-- The recorded exact extension by zero, derived termwise.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodOpenLowerShriek {A B : Scheme.{u}} (a : A ⟶ B) [IsOpenImmersion a] :
    PodDerived Λ A ⥤ PodDerived Λ B :=
  (openImmersionLowerShriek Λ a).mapDerivedCategory

/-- The dependency compactification lower shriek, in diagrammatic functor order.
Source: clauses (1), (3), module-derived convention
(blueprint: lem-pod-condensed-compactification-square-transport). -/
abbrev PodCompactSupport {A B : Scheme.{u}} {f : A ⟶ B}
    (c : Compactification f) : PodDerived Λ A ⥤ PodDerived Λ B :=
  rightDerivedLowerShriekOfCompactification Λ c

/-- Transport a literal pullback compactification through the supplied source and ambient
scheme isomorphisms.
Source: coordinate paragraph of clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedCompactification {X X' Z Y : Scheme.{u}}
    {f : X' ⟶ Y} (c : Compactification f) (eX : X ≅ X') (eZ : Z ≅ c.Z) :
    Compactification (eX.hom ≫ f) where
  Z := Z
  g := eZ.hom ≫ c.g
  i := eX.hom ≫ c.i ≫ eZ.inv
  comm := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun a ↦ eX.hom ≫ a) c.comm
  isProper := inferInstance
  isOpenImmersion := inferInstance

/-- The literal pulled-back boundary compactification.
Source: base change in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podPullbackBoundary {X Y Y' : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (v : Y' ⟶ Y) :
    Compactification.BoundaryCompactification (pullback.snd f v) :=
  detSfBoundaryCompactification (c.obj.obj.baseChange v)

/-- The realized boundary compactification, with the prescribed coordinate formulas.
Source: the coordinate paragraph in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedBoundary {X X' Z Y : Scheme.{u}} {f : X' ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (eX : X ≅ X')
    (eZ : Z ≅ c.obj.obj.Z) :
    Compactification.BoundaryCompactification (eX.hom ≫ f) :=
  detSfBoundaryCompactification (podRealizedCompactification c.obj.obj eX eZ)

/-- The comparison chi, formed from precisely its proper mate and open exchange factors.
Source: the displayed definition of chi in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podCompactificationComparison {A B T Z : Scheme.{u}} {f : A ⟶ B}
    (c : Compactification f) (eX : T ≅ A) (eZ : Z ≅ c.Z)
    (q : PodPushforward Λ c.g ≅
      PodPullback Λ eZ.hom ⋙ PodPushforward Λ (eZ.hom ≫ c.g))
    (b : PodOpenLowerShriek Λ c.i ⋙ PodPullback Λ eZ.hom ≅
      PodPullback Λ eX.hom ⋙
        PodOpenLowerShriek Λ (podRealizedCompactification c eX eZ).i) :
    PodCompactSupport Λ c ≅
      PodPullback Λ eX.hom ⋙
        PodCompactSupport Λ (podRealizedCompactification c eX eZ) :=
  Functor.isoWhiskerLeft (PodOpenLowerShriek Λ c.i) q ≪≫
    Functor.isoWhiskerRight b (PodPushforward Λ (eZ.hom ≫ c.g))

/-- The realized pullback as a boundary compactification; its arrows are the coordinate
formulas, and its quasi-compactness follows from that of f.
Source: coordinate paragraph of clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRealizedPullbackBoundary {X Y Y' T Z : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification.BoundaryCompactification f) (v : Y' ⟶ Y)
    (eX : T ≅ pullback f v) (eZ : Z ≅ pullback c.obj.obj.g v) :
    Compactification.BoundaryCompactification (eX.hom ≫ pullback.snd f v) :=
  podRealizedBoundary (podPullbackBoundary c v) eX eZ

/-- The dependency's normalized direct-image compositor, including the refinement triangle's
canonical equality identification. Its inverse is exactly the proper factor in rho.
Source: refinement formula in clauses (1), (3)
(blueprint: lem-pod-condensed-compactification-square-transport). -/
def podRefinementDirectImage {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c) :
    PodPushforward Λ d.obj.obj.g ≅
      PodPushforward Λ h.hom.hom.hom ⋙ PodPushforward Λ c.obj.obj.g :=
  (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ h.hom.hom.hom_g)).symm ≪≫
    refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g

set_option maxHeartbeats 1600000 in
-- The normalized refinement equations across several derived functors need this budget.
end AlgebraicGeometry.ProEtale.CondensedRing
