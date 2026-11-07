/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Submission.WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Submission.WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Unbounded derived direct image on ringed spaces

Source: Stacks Project, Cohomology, Section 20.28 (Tag 079V), construction preceding
Tag 079W (blueprint: def-pc-ringed-spaces-derived-direct-image).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The Grothendieck structure supplied by the small-site resolution theorem.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleGrothendieckAbelian (X : RingedSpace.{u}) :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
  (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
    (Opens.grothendieckTopology X) X.sheaf).1

/-- Specialization of Mathlib's module pushforward to a ringed-space morphism.
Its sections on V are the sections on the inverse image of V, with scalar action
through g-sharp, and its map on morphisms is the component on that inverse image.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def moduleDirectImage {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    SheafOfModules.{u} (moduleRings X) ⥤ SheafOfModules.{u} (moduleRings Y) :=
  SheafOfModules.pushforward (F := Opens.map g.hom.base)
    (R := moduleRings X) (S := moduleRings Y)
    ⟨Functor.whiskerRight g.hom.c (forget₂ CommRingCat RingCat)⟩

/-- Module direct image is additive, hence its termwise action carries homotopies
and homotopy equivalences to homotopies and homotopy equivalences.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: sums and zero maps of module sheaves are computed on sections. Direct image
uses exactly the same maps on inverse-image opens, so preserves these operations. -/
theorem moduleDirectImage_additive_proof {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    (moduleDirectImage g).Additive := by
  constructor
  intro A B f h
  rfl

/-- Additivity of module direct image. Source: Stacks, Tag 079V
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
instance moduleDirectImage_additive {X Y : RingedSpace.{u}} (g : X ⟶ Y) :
    (moduleDirectImage g).Additive := moduleDirectImage_additive_proof g

variable {X Y : RingedSpace.{u}}
  [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X))]
  [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y))]

/-- Resolve functorially, apply direct image termwise, and localize on the target.
The resolution functor and its natural quasi-isomorphism are the existing
`CochainComplex.kInjectiveResolutionFunctor` and `toKInjectiveResolution`.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image). -/
def resolvedModuleDirectImage (g : X ⟶ Y) :
    CochainComplex (SheafOfModules.{u} (moduleRings X)) ℤ ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  CochainComplex.kInjectiveResolutionFunctor.{u} (SheafOfModules.{u} (moduleRings X)) ⋙
    (moduleDirectImage g).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q


/-- The unbounded derived direct image: the right derived functor
`CategoryTheory.Functor.rightDerivedFunctor` (the landed unbounded right derived functor
of an additive functor on a category with K-injective resolutions) of the module direct
image. It is computed by K-injective resolutions: its unit is an isomorphism on every
K-injective complex. The K-injective resolutions come from `moduleGrothendieckAbelian`.
Source: Stacks, Tag 079V, preceding Tag 079W
(blueprint: def-pc-ringed-spaces-derived-direct-image). -/
abbrev derivedModuleDirectImage (g : X ⟶ Y) :
    DerivedCategory (SheafOfModules.{u} (moduleRings X)) ⥤
      DerivedCategory (SheafOfModules.{u} (moduleRings Y)) :=
  (moduleDirectImage g).rightDerivedFunctor

/-- The defining comparison: Q followed by Rg-star is isomorphic to the functorial
K-injective resolution followed by termwise g-star and Q, so Rg-star(QK) = Q(g-star I(K))
and Rg-star(Q f) = Q(g-star I(f)) up to this natural isomorphism.
Source: Stacks, Tag 079V (blueprint: def-pc-ringed-spaces-derived-direct-image).
Proof: the unit of the right derived functor is an isomorphism on the K-injective
complexes I(K); compose it with Rg-star applied to the inverse of Q of the natural
quasi-isomorphism K to I(K), which is natural in K. -/
theorem derivedModuleDirectImageFactorization (g : X ⟶ Y) :
    Nonempty (DerivedCategory.Q ⋙ derivedModuleDirectImage g ≅ resolvedModuleDirectImage g) := by
  let C := SheafOfModules.{u} (moduleRings X)
  let D := SheafOfModules.{u} (moduleRings Y)
  let F := moduleDirectImage g
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} C
  let η := CochainComplex.toKInjectiveResolution.{u} C
  let γ : DerivedCategory.Q ⟶ I ⋙ DerivedCategory.Q :=
    Functor.whiskerRight η DerivedCategory.Q
  have hγ : IsIso γ := by
    have (K : CochainComplex C ℤ) : IsIso (γ.app K) := by
      have : QuasiIso (η.app K) :=
        (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} C K).2
      change IsIso (DerivedCategory.Q.map (η.app K))
      infer_instance
    exact NatIso.isIso_of_isIso_app γ
  let β : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
    (Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso D)).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient C (ComplexShape.up ℤ))
      F.rightDerivedFunctorUnit ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C) F.rightDerivedFunctor).hom
  have hβ : IsIso (Functor.whiskerLeft I β) := by
    have (K : CochainComplex C ℤ) : IsIso ((Functor.whiskerLeft I β).app K) := by
      dsimp [β]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact ⟨asIso (Functor.whiskerRight γ F.rightDerivedFunctor) ≪≫
    (asIso (Functor.whiskerLeft I β)).symm⟩


end AlgebraicGeometry.RingedSpace
