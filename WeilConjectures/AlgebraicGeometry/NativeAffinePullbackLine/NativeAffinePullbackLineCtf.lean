/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorShift
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocallyFreeTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.AlgebraicGeometry.Pullback.PullbackFiniteConstantLocalModel

/-! # Exact pullback and shifted line tensor preserve finite constructible Tor amplitude

Source: latest blueprint, sk-prop-sf-rf-shriek-preservation.proof.md, affine-projection
paragraph, final sentence (blueprint: lem-sf-native-affine-pullback-line-ctf).

The coefficients remain the pulled-back condensed ring. The representative comparison
is the localization tensorator, followed by the canonical single-complex and shift
identifications; no arbitrary comparison is selected.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.NativeAffinePullbackLine

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Internal modules over the existing pulled-back coefficient ring.
Source: blueprint affine-projection paragraph
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
abbrev Modules (X : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)

/-- The ordinary unbounded derived category of these internal modules.
Source: blueprint affine-projection paragraph
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
abbrev D (X : Scheme.{u}) := DerivedCategory (Modules Λ X)

/-- The exact module inverse image induced on ordinary derived categories.
This is the published total left derived pullback, canonically identified with the
exact induced functor by `Functor.leftDerivedFunctorIsoMapDerivedCategory`.
Source: blueprint affine-projection paragraph
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
def pull {X Y : Scheme.{u}} (f : X ⟶ Y) : D Λ Y ⥤ D Λ X :=
  CondensedRing.moduleObjectDerivedPullback Λ f

/-- The literal termwise complex `(f^* C ⊗ L)[n]`.
Source: blueprint affine-projection paragraph, bounded flat model
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
def lineComplex {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Modules Λ X)
    (n : ℤ) (C : CochainComplex (Modules Λ Y) ℤ) :
    CochainComplex (Modules Λ X) ℤ :=
  (((tensorRight L).mapHomologicalComplex (.up ℤ)).obj
    (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj C))⟦n⟧

/-- The literal derived tensor `f^* K ⊗ᴸ L[n]`.
Source: blueprint affine-projection paragraph
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
def lineObject {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Modules Λ X)
    (n : ℤ) (K : D Λ Y) : D Λ X :=
  (pull Λ f).obj K ⊗ ((DerivedCategory.singleFunctor _ 0).obj L)⟦n⟧

/-- The canonical total-tensor to termwise shifted single-tensor identification.
Source: blueprint affine-projection paragraph, representative calculation
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
def totalLineIso {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Modules Λ X)
    (n : ℤ) (C : CochainComplex (Modules Λ Y) ℤ) :
    (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj C) ⊗
        (((HomologicalComplex.single _ (.up ℤ) 0).obj L)⟦n⟧) ≅
      lineComplex Λ f L n C :=
  ((curriedTensor (Modules Λ X)).map₂CochainComplexFlipObjShiftIso
    ((HomologicalComplex.single _ (.up ℤ) 0).obj L) n).app _ ≪≫
  (shiftFunctor _ n).mapIso
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Modules Λ X)) L _)

/-- The canonical comparison from derived tensor to the localized termwise model.
Its direction is the usual left-derived counit direction. It is defined for every
complex; invertibility for the bounded flat constructible representatives is asserted
below. The only inputs are the given representative isomorphism and canonical maps.
Source: blueprint affine-projection paragraph, representative calculation
(blueprint: lem-sf-native-affine-pullback-line-ctf). -/
def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) (L : Modules Λ X)
    (n : ℤ) (C : CochainComplex (Modules Λ Y) ℤ) (K : D Λ Y)
    (e : DerivedCategory.Q.obj C ≅ K) :
    lineObject Λ f L n K ⟶ DerivedCategory.Q.obj (lineComplex Λ f L n C) :=
  (((pull Λ f).map e.inv ≫
      (CondensedRing.upperStar Λ f).leftDerivedFunctorIsoMapDerivedCategory.hom.app
        (DerivedCategory.Q.obj C) ≫
      (CondensedRing.upperStar Λ f).mapDerivedCategoryFactors.hom.app C) ⊗ₘ
    ((shiftFunctor _ n).map ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app L) ≫
      (DerivedCategory.Q.commShiftIso n).inv.app
        ((HomologicalComplex.single _ (.up ℤ) 0).obj L))) ≫
  Functor.LaxMonoidal.μ (DerivedCategory.Q (C := Modules Λ X))
    (((CondensedRing.upperStar Λ f).mapHomologicalComplex (.up ℤ)).obj C)
    (((HomologicalComplex.single _ (.up ℤ) 0).obj L)⟦n⟧) ≫
  DerivedCategory.Q.map (totalLineIso Λ f L n C).hom

omit [IsCommMonObj Λ] in
set_option maxHeartbeats 600000 in
-- Compare the exact derived functors before specializing the coefficient object.
end AlgebraicGeometry.ProEtale.NativeAffinePullbackLine

namespace AlgebraicGeometry.ProEtale

open NativeAffinePullbackLine

end AlgebraicGeometry.ProEtale
