/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRingCompactSupport.FiniteRingCanonicalCompactSupport
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.SchemeFrobeniusFiniteRadicial
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedPoint.NativeCondensedPointSections
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCanonicalPullbackComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizationFiniteTor
public import WeilConjectures.SixFunctors.ProEtale.AlgClosedFieldSite
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Restriction
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTrans
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleObjectInverseImageRestrictionSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModulePullbackComposition
import WeilConjectures.AlgebraicGeometry.ProEtaleTensorCompositionUnit
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Data.PNat.Basic

/-! # Canonical finite-ring Frobenius compact-support transport

Source: latest blueprint, lem-trf-frobenius-operator-compact-description, power clause;
released finite-ring repair P1 (blueprint: lem-trf-compact-frobenius-transport-composition).
Compactifications below are computational representatives quantified in the conclusion,
never additional data of a Weil pair. All functors are ordinary and uncompleted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open AlgebraicGeometry.ProEtale
namespace WeilConjectures.CompactFrobeniusTransport

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable (D : FiniteFieldDatum.{u})

/-- The coefficient automorphism Spec(gamma), gamma inverse q-power.
Source: Weil II (1.1.7)
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def point : Aut (Spec (CommRingCat.of D.k)) :=
  letI : Fintype D.k₀ := Fintype.ofFinite D.k₀
  Scheme.Spec.mapIso
    (FiniteField.geometricFrobeniusAlgEquivOfAlgebraic D.k₀ D.k).toRingEquiv.toCommRingCatIso.op

/-- Termwise exact sections, descended to the ordinary derived category.
Source: point-sections dependency
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
abbrev sections :=
  (Sheaf.Γ (Scheme.ProEt.topology (Spec (CommRingCat.of D.k)))
    (ModuleCat.{u + 1} A)).mapDerivedCategory

/-- Derived pullback by the r-th point Frobenius.
Source: ordinary finite coefficient operations
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
abbrev pointPullback (r : ℕ) :=
  (upperStar (ModuleCat.{u + 1} A) ((point D) ^ r).hom).leftDerivedFunctor

/-- The specified localized restriction insertion. The underived transformation is
sections of the pullback adjunction unit, hence restriction, the colimit coprojection,
sheafification and tensor with 1. Its localization uses the canonical L-to-exact
comparison, rather than any chosen isomorphism.
Source: Stacks 03CE, 03D3, 06UM and the point-insertion dependency
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def insertion (r : ℕ) : sections A D ⟶ pointPullback A D r ⋙ sections A D :=
  Functor.mapDerivedCategoryNatTrans
      (globalSectionsToUpperStar (ModuleCat.{u + 1} A) ((point D) ^ r).hom) ≫
    (Functor.mapDerivedCategoryCompIso _ _).hom ≫
    (Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{u + 1} A) ((point D) ^ r).hom).symm (sections A D)).hom

variable (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [hsep : IsSeparated X₀.hom]

/-- Ordinary derived pullback P_r along the actual r-th geometric Frobenius.
Source: scheme-Frobenius dependency
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
abbrev pullback (r : ℕ) :=
  (upperStar (ModuleCat.{u + 1} A) ((D.geometricFrobenius X₀) ^ r).hom).leftDerivedFunctor

omit hsep in
/-- The inverse of the normalized derived pullback compositor, P_1 P_m to P_(m+1).
Source: derived-pullback-composition dependency
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def compositor (m : ℕ) : pullback A D X₀ m ⋙ pullback A D X₀ 1 ≅
    pullback A D X₀ (m + 1) :=
  (leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
    (D.geometricFrobenius X₀).hom ((D.geometricFrobenius X₀) ^ m).hom).symm ≪≫
    leftDerivedUpperStarCongr (ModuleCat.{u + 1} A)
      (congrArg Iso.hom (pow_succ (D.geometricFrobenius X₀) m)).symm

/-- Compact-support cohomology in a representative of its canonically identified family.
Source: finite-ring compact-support comparison dependency
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
abbrev cohomology (c : Compactification (D.geometricFiber X₀).hom) :=
  FiniteRingCompactSupport.support A c ⋙ sections A D

/-- The actual finite compact-support exchange followed after point insertion.
Source: blueprint power formula and proper/open exchange
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def transport (c : Compactification (D.geometricFiber X₀).hom) (r : ℕ)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K) :
    (cohomology A D X₀ c).obj K ⟶
      (cohomology A D X₀ c).obj ((pullback A D X₀ r).obj K) :=
  (insertion A D r).app ((FiniteRingCompactSupport.support A c).obj K) ≫
    (sections A D).map
      (FiniteRingCompactSupport.exchange A (square D X₀ r) c c K
        (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK).plusEtaleOrigin)

/-- Successive degree-one transport, inserting exactly the canonical compositors.
The natural-number index n denotes n+1 steps.
Source: blueprint power clause
(blueprint: lem-trf-compact-frobenius-transport-composition). -/
def successive (c : Compactification (D.geometricFiber X₀).hom)
    (K : FiniteRingCompactSupport.Category A (D.geometricFiber X₀).left)
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor
      (ModuleCat.{u + 1} A) (D.geometricFiber X₀).left K) :
    (n : ℕ) → (cohomology A D X₀ c).obj K ⟶
      (cohomology A D X₀ c).obj ((pullback A D X₀ (n + 1)).obj K)
  | 0 => transport A D X₀ c 1 K hK
  | n + 1 => successive c K hK n ≫
      transport A D X₀ c 1 ((pullback A D X₀ (n + 1)).obj K)
        (constructibleFiniteTor_leftDerivedFunctor_upperStar_obj _ hK) ≫
      (cohomology A D X₀ c).map ((compositor A D X₀ (n + 1)).hom.app K)

include hsep in
end WeilConjectures.CompactFrobeniusTransport
