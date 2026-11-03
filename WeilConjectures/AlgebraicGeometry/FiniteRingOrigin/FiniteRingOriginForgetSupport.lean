/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1CompactificationFibre.P1CompactificationFibre
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.SixFunctors.Etale.SupportCohomologyHom
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.AlgebraicGeometry.KummerLine.KummerAffineLineArbitrary2
import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Origin-normalized compact support for arbitrary finite coefficient rings

Source: blueprint sec-smooth-purity/sk-prop-an/thm-pur-rank-one-thom.proof.md,
Step 2; released repair note of 2026-11-01
(blueprint: lem-pur-finite-origin-forget-support).

The definitions use the published Kummer splice, compactification and comparison
maps. The coefficient ring is an arbitrary finite commutative ring; no
PurityFiniteSetting is used in these statements.
The origin-normalized proof route retains its recorded BLUEPRINT QUESTION.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Etale AlgebraicGeometry.Etale.P1CompactificationFibre

namespace AlgebraicGeometry.Etale.FiniteRingOrigin


/-- The existing scalar extension of roots of unity, without a freeness hypothesis.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev twist (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (T : Scheme.{u}) := Scheme.finiteEtaleTateLine T m A hA

/-- Degree-zero embedding of the published finite twist.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev coefficient (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (T : Scheme.{u}) := (DerivedCategory.singleFunctor _ 0).obj (twist A m hA T)

/-- Derived sections supported at the actual zero section.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev supported (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (S : Scheme.{u}) :=
  (rightDerivedSectionsWithSupport (C A) (z S)).obj
    (coefficient A m hA (𝔸(PUnit.{u + 1}; S)))

/-- Compact support from the compact-support direct image, followed by base sections.
Source: def-amb-etale-compact-support, blueprint Step 2
(blueprint: lem-pur-finite-origin-forget-support). -/
abbrev compact (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (S : Scheme.{u}) :=
  (rightDerivedGlobalSections (C A) S).obj
    ((rightDerivedLowerShriekOfCompactification (C A) (compactification S)).obj
      (coefficient A m hA (𝔸(PUnit.{u + 1}; S))))

/-- Forget the proper support by excision and the support-kernel inclusion, followed
by the canonical compactification identification. No trace normalization occurs here.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def forget (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (S : Scheme.{u}) : supported A m hA S ⟶ compact A m hA S :=
  (excision S A (twist A m hA (𝔸(PUnit.{u + 1}; S)))).hom ≫
    (forgetSupport S A).app _ ≫
      (compactSupportComparison S A (twist A m hA (𝔸(PUnit.{u + 1}; S)))).hom

/-- The finite-comparison presentation of pro-etale compact support. The canonical
extension-by-zero comparison identifies the inner object with j! of the pulled-back twist.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
abbrev proCompact (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (S : Scheme.{u}) :=
  (ProEtale.rightDerivedGlobalSections (C A) (ProjectiveLine S)).obj
    ((ProEtale.comparisonUpperStar (C A) (ProjectiveLine S)).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((openImmersionLowerShriek (C A) (j S)).obj
          (twist A m hA (𝔸(PUnit.{u + 1}; S))))))

/-- The compactification identification followed by the canonical global comparison.
Source: blueprint Step 2 (blueprint: lem-pur-finite-origin-forget-support). -/
def compareCompact (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (S : Scheme.{u}) : compact A m hA S ⟶ proCompact A m hA S :=
  (compactSupportComparison S A (twist A m hA (𝔸(PUnit.{u + 1}; S)))).inv ≫
    (rightDerivedGlobalSections (C A) (ProjectiveLine S)).map
      ((ProEtale.derivedComparisonAdjunction (C A) (ProjectiveLine S)).unit.app _) ≫
    (ProEtale.comparisonLowerStarCompRightDerivedGlobalSectionsIso (C A)
      (ProjectiveLine S)).hom.app _

end AlgebraicGeometry.Etale.FiniteRingOrigin
