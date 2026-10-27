/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.CanonicalOriginCompactSupportComposition
public import Sheaf.Paper.CompactSupportSiteCoherence
public import Sheaf.AlgebraicGeometry.CompactSupportRestrictionOfScalars
public import Sheaf.Paper.ExceptionalCoefficientComparison
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.FiniteCoefficientAdjointComparisons
public import Sheaf.Paper.FiniteCoefficientDirectImage
public import Sheaf.Paper.FiniteFreeCoefficientExtension
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.ProEtaleConstructibleOrigin
public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.RefinementComparisonIsomorphism
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-! # Finite-free coefficient extension and compact-support composition

Source: blueprint main-20261015, sec-smooth-purity/sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: def-pur-finite-free-compact-support-data).
The two Boolean cases are the ordinary small etale site and its pro-etale realization.
All equations live in the B-linear derived category. The proper and open maps, and
both geometric comparisons, are the existing normalized constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
open AlgebraicGeometry
open WeilConjectures.FiniteFreeCoefficients
open AlgebraicGeometry.FiniteCoefficientAdjoints

namespace AlgebraicGeometry.FiniteFreeCompactSupport

/-- Realization of an ordinary etale object on the selected site.
Source: blueprint transport Step 8 (blueprint: def-pur-finite-free-compact-support-data). -/
def realization (pro : Bool) (A : Type (u + 1)) [CommRing A] (X : Scheme.{u}) :
    Etale.DerivedCategoryModule A X ⥤ Sites.D pro A X := by
  cases pro
  · exact 𝟭 _
  · exact Sites.nu A X

/-- The existing compactification candidate, on either of the two ordinary small sites.
Source: blueprint transport Steps 2 and 8
(blueprint: def-pur-finite-free-compact-support-data). -/
def support (pro : Bool) (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Sites.D pro A X ⥤ Sites.D pro A Y := by
  cases pro
  · exact Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c
  · exact ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- The specified coefficient map: the existing extended-counit proper map followed
by the balancing open map. In the pro-etale presentation it is the existing universal
scalar-adjunction formula for precisely those constituents.
Source: blueprint transport Steps 2 and 8
(blueprint: def-pur-finite-free-compact-support-data). -/
def coefficientMap (pro : Bool) {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (K : Sites.D pro A X) :
    (Sites.scalar pro φ Y).obj ((support pro A c).obj K) ⟶
      (support pro B c).obj ((Sites.scalar pro φ X).obj K) := by
  cases pro
  · exact Etale.ExceptionalCoefficients.compactSupportMap φ c K
  · exact ((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ)).homEquiv _ _).symm
      ((support true A c).map
        ((Adjunction.ofIsRightAdjoint
          (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ)).unit.app K) ≫
        (ProEtale.compactSupportRestrictionIso φ c).hom.app
          ((Sites.scalar true φ X).obj K))

/-- The canonical etale compositor in the ambient derived categories; only the
published D-plus compatibility isomorphisms are inserted.
Source: blueprint transport Steps 4--7
(blueprint: def-pur-finite-free-compact-support-data). -/
def etaleComposition (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support false A d).obj ((support false A c).obj L.obj) ⟶
      (support false A e).obj L.obj :=
  (support false A d).map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).inv.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).inv.app
        ((Etale.rightDerivedLowerShriekOfCompactificationPlus
          (ModuleCat.{u + 1} A) c).obj L) ≫
    DerivedCategory.Plus.ι.map ((ProEtale.coherenceEtaleCompositor A c d e).hom.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) e).hom.app L

/-- The actual canonical composition map at an etale realization.
Source: blueprint transport Steps 4--8
(blueprint: def-pur-finite-free-compact-support-data). -/
def compositionReal (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support pro A d).obj ((support pro A c).obj ((realization pro A X).obj L.obj)) ⟶
      (support pro A e).obj ((realization pro A X).obj L.obj) := by
  cases pro
  · exact etaleComposition A c d e L
  · exact ProEtale.coherenceProEtaleCompositor A c d e L

/-- Composition at an arbitrary retained origin witness, by canonical naturality.
Source: blueprint transport Steps 7--8
(blueprint: def-pur-finite-free-compact-support-data). -/
def composition (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [QuasiCompact f] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g) (e : Compactification (f ≫ g))
    {K : Sites.D pro A X}
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (realization pro A X).obj L.obj ≅ K) :
    (support pro A d).obj ((support pro A c).obj K) ⟶ (support pro A e).obj K :=
  (support pro A d).map ((support pro A c).map α.inv) ≫
    compositionReal pro A c d e L ≫ (support pro A e).map α.hom

/-- The inverse of the recorded etale refinement comparison, in ambient categories.
Its direction is from the dominating compactification c to d.
Source: blueprint transport Step 3
(blueprint: def-pur-finite-free-compact-support-data). -/
def etaleRefinement (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (support false A c).obj L.obj ⟶ (support false A d).obj L.obj :=
  (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) c).inv.app L ≫
    DerivedCategory.Plus.ι.map
      ((Etale.rightDerivedLowerShriekOfCompactificationPlusRefinementIso A r).inv.app L) ≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
      (ModuleCat.{u + 1} A) d).hom.app L

/-- The actual proper-refinement arrow on each site, evaluated at a retained witness.
Source: blueprint transport Steps 3 and 8
(blueprint: def-pur-finite-free-compact-support-data). -/
def refinement (pro : Bool) (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {c d : Compactification f} (r : c.Refinement d)
    {K : Sites.D pro A X}
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (α : (realization pro A X).obj L.obj ≅ K) :
    (support pro A c).obj K ⟶ (support pro A d).obj K :=
  (support pro A c).map α.inv ≫ (by
    cases pro
    · exact etaleRefinement A r L
    · exact (ProEtale.properTransportRefinement A r L).hom) ≫
    (support pro A d).map α.hom

/-- The coefficient/site square, with the proper/open site comparisons and the
scalar/site balancing explicitly inserted. N and gamma merely present the bounded
scalar extension of L; every possible such presentation is allowed.
Source: blueprint transport Step 8
(blueprint: def-pur-finite-free-compact-support-data). -/
def SiteCompatibility {A B : Type (u + 1)} [CommRing A] [CommRing B]
    [Finite A] [Finite B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
    (γ : N.obj ≅ (Sites.scalar false φ X).obj L.obj) : Prop :=
  coefficientMap true φ c ((Sites.nu A X).obj L.obj) =
    (Sites.scalar true φ Y).map
        ((ProEtale.compactSupportSiteComparison A c).hom.app L) ≫
      (Sites.scalarSite φ Y).hom.app ((support false A c).obj L.obj) ≫
      (Sites.nu B Y).map (coefficientMap false φ c L.obj) ≫
      (Sites.nu B Y).map ((support false B c).map γ.inv) ≫
      (ProEtale.compactSupportSiteComparison B c).inv.app N ≫
      (support true B c).map ((Sites.nu B X).map γ.hom) ≫
      (support true B c).map ((Sites.scalarSite φ X).inv.app L.obj)

end AlgebraicGeometry.FiniteFreeCompactSupport
