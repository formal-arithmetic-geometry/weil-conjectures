/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.OrdinaryScalarSite.OrdinaryScalarSiteComparisons
public import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportComparisons
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableOverField
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Finite coefficient compact-support comparison

Source: `literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-change-of-finite-coefficients/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md` (det-sp-reduction-exceptional), Charts and Locality;
Stacks 0GL6, 0F7I, 0F7J.
(blueprint: lem-sp-et-proet-coefficient-compatibility).

All constructions use ordinary constant-coefficient module sheaves, the finite discrete
presentation of pulled-back condensed coefficients. Scalar extension
is the published left adjoint to actual exact scalar restriction. Proper coefficient
maps are its geometric counit mates; open and etale sum comparisons are the unique
comparisons of the specified composite adjunctions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.FiniteCompactCoefficients
open OrdinaryScalarSite

/-- The recorded ordinary etale compact-support candidate.
Source: Stacks 0F7I (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev et (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c

/-- The recorded ordinary pro-etale compact-support candidate.
Source: Charts (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev pro (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :=
  rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} R) c

/-- Exact comparison pullback, localized termwise.
Source: Stacks 099R (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev nu (R : Type (u + 1)) [CommRing R] (X : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} R) X).mapDerivedCategory

/-- The same unit-normalized open scalar comparison on the pro-etale site.
Source: Stacks 03S2, 06YY (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def proOpen {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalar (Scheme.ProEt.topology Z) a ≅
      scalar (Scheme.ProEt.topology X) a ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory :=
  ((Adjunction.mapDerivedCategoryAdjunction
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).comp
        (CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology Z) a)).ofNatIsoRight
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a j))
    |>.leftAdjointUniq
      ((CoefficientScalarRepresentatives.adjunction (Scheme.ProEt.topology X) a).comp
        (Adjunction.mapDerivedCategoryAdjunction
          (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)))

/-- The intrinsic pro-etale coefficient map b, using the geometric B-linear counit mate.
Source: Charts (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def b {A B : Type (u + 1)} [CommRing A] [CommRing B] (a : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    pro A c ⋙ scalar (Scheme.ProEt.topology Y) a ⟶
      scalar (Scheme.ProEt.topology X) a ⋙ pro B c :=
  Functor.whiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory
      (proEtaleGamma a c.g) ≫
    Functor.whiskerRight (proOpen a c.i).hom
      (lowerStar (ModuleCat.{u + 1} B) c.g).rightDerivedFunctor

/-- The specified compact-support site comparison c: proper counit mate, then open mate.
It is defined before asserting that it is invertible.
Source: Stacks 099R, 09AF (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
def site (R : Type (u + 1)) [CommRing R]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    et R c ⋙ nu R Y ⟶ nu R X ⋙ pro R c :=
  Functor.whiskerLeft
      (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} R) c.i).mapDerivedCategory
      (ambientEtaleProEtaleDirectImageComparison R c.g) ≫
    Functor.whiskerRight
      (Functor.mapDerivedCategorySquareIso
        (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} R) c.i)).hom
      (lowerStar (ModuleCat.{u + 1} R) c.g).rightDerivedFunctor

/-- Bounded constructibility and the uniform degree-zero-sheaf tensor bound in the node.
This abbreviates the recorded predicates; no flatness condition is imposed on B/A.
Source: finite coefficient paragraph (blueprint: lem-sp-et-proet-coefficient-compatibility). -/
abbrev Input (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (L : Etale.DerivedCategoryModule R X) : Prop :=
  Etale.DerivedCategory.isBoundedConstructible R X L ∧
    ∃ m n : ℤ, m ≤ n ∧ Etale.DerivedCategory.hasTorAmplitudeIn R X m n L

section Setting
variable (ℓ : ℕ) [hℓprime : Fact ℓ.Prime] (k : Type u) [Field k]
  [hkchar : Fact (ringChar k).Prime] [hkne : Fact (ringChar k ≠ ℓ)]
  {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
  (hA : ∃ n : ℕ, ∀ x : A, (ℓ ^ n) • x = 0)
  (hB : ∃ n : ℕ, ∀ x : B, (ℓ ^ n) • x = 0)
  (a : A →+* B)
  {X Y : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [hXft : LocallyOfFiniteType (X ↘ Spec (.of k))]
  [hXqc : QuasiCompact (X ↘ Spec (.of k))]
  [hXs : IsSeparated (X ↘ Spec (.of k))]
  [hYft : LocallyOfFiniteType (Y ↘ Spec (.of k))]
  [hYqc : QuasiCompact (Y ↘ Spec (.of k))]
  [hYs : IsSeparated (Y ↘ Spec (.of k))]
  {f : X ⟶ Y} [hfov : f.IsOver (Spec (.of k))]
  [hfs : IsSeparated f] [hfft : LocallyOfFiniteType f] [hfqc : QuasiCompact f]
include hℓprime hkchar hkne hA hB hXft hXqc hXs hYft hYqc hYs hfov hfs hfft hfqc

end Setting
end AlgebraicGeometry.ProEtale.FiniteCompactCoefficients
