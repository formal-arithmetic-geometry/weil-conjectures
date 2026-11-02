/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedRealization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionDerivedPushpullNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionMateTranspose

/-!
# Native condensed compact-support section coordinates

Source: latest blueprint, sec-six-functors-basics/sk-prop-qlbar-two-colimit/
det-def-sf-operations.md (iv), and sec-proetale-coefficients/
sk-prop-sf-open-closed-triangle/det-def-sfb-bounded-constructible.md
(blueprint: def-pur-integral-support-coordinate-comparison).

All operations are the recorded ordinary and derived module operations. The construction
works for every commutative condensed ring and compactification, so in particular for
all the admissible coefficients and separated finite-type schemes over the field in
the node. No field or admissibility choice enters any component. All derived categories
are ordinary unbounded derived categories. The sites have object universe u+1 and Hom
universe u, with coefficient sections in u+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- The separately derived section-module compactification expression: exact open
extension followed by total right-derived proper direct image.
Source: det-def-sf-operations (iv)
(blueprint: def-pur-integral-support-coordinate-comparison). -/
def sectionSupport (c : Compactification f) :
    DerivedCategory (modules Λ X) ⥤ DerivedCategory (modules Λ Y) :=
  derivedExtension Λ c.i ⋙ derivedPushforward Λ c.g

/-- The ordinary and derived maps whose equations specify the comparison package.
Each endpoint uses the fixed section-action equivalence and the actual operations.
Source: det-def-sf-operations (iv), proper/open coordinate construction
(blueprint: def-pur-integral-support-coordinate-comparison). -/
structure SupportCoordinatePackage (c : Compactification f) where
  /-- Ordinary direct image for the open map. -/
  openPush : CondensedRing.lowerStar Λ c.i ⋙ (equivalence Λ c.Z).functor ≅
    (equivalence Λ X).functor ⋙ pushforward Λ c.i
  /-- Ordinary direct image for the proper map. -/
  properPush : CondensedRing.lowerStar Λ c.g ⋙ (equivalence Λ Y).functor ≅
    (equivalence Λ c.Z).functor ⋙ pushforward Λ c.g
  /-- The inverse-image comparison, the inverse mate of openPush. -/
  openPull : CondensedRing.upperStar Λ c.i ⋙ (equivalence Λ X).functor ≅
    (equivalence Λ c.Z).functor ⋙ pullback Λ c.i
  /-- The extension-by-zero comparison fixed by open Hom transposition. -/
  openExtension : CondensedRing.openImmersionLowerShriek Λ c.i ⋙
      (equivalence Λ c.Z).functor ≅ (equivalence Λ X).functor ⋙ extension Λ c.i
  /-- Exact termwise localization of openExtension. -/
  derivedOpen : internalDerivedExtension Λ c.i ⋙ (derivedEquivalence Λ c.Z).functor ≅
    (derivedEquivalence Λ X).functor ⋙ derivedExtension Λ c.i
  /-- The comparison normalized by the full right-derived unit on every complex. -/
  derivedProper : internalDerivedPushforward Λ c.g ⋙ (derivedEquivalence Λ Y).functor ≅
    (derivedEquivalence Λ c.Z).functor ⋙ derivedPushforward Λ c.g

/-- The canonical package uses the existing fixed comparisons, with no new choices.
Source: det-def-sf-operations (iv), ordinary and derived section realizations
(blueprint: def-pur-integral-support-coordinate-comparison). -/
def supportCoordinatePackage (c : Compactification f) : SupportCoordinatePackage Λ c where
  openPush := pushComparison Λ c.i
  properPush := pushComparison Λ c.g
  openPull := pullComparison Λ c.i
  openExtension := extensionComparison Λ c.i
  derivedOpen := derivedExtensionComparison Λ c.i
  derivedProper := derivedPushComparison Λ c.g

set_option maxHeartbeats 1200000 in
-- Identifying six comparison fields requires elaborating the fixed coordinate functors.
/-- The native condensed proper/open section-coordinate comparison beta.
Its components are Rg*(q_M) after p_(J_i M); no second compact-support functor is derived.
Source: det-def-sf-operations (iv)
(blueprint: def-pur-integral-support-coordinate-comparison). -/
def supportCoordinateComparison (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        (derivedEquivalence Λ Y).functor ≅
      (derivedEquivalence Λ X).functor ⋙ sectionSupport Λ c :=
  (supportCoordinatePackage Λ c).beta Λ c

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
