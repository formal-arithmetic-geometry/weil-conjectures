/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.AlgebraicGeometry.CompactProductRealizationArrows
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProperSupportCompactMaps
public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.Paper.SupportedClassGeometry

/-! # Core finite-site compact-product comparison clauses

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry AlgebraicGeometry.Etale


/-- The output representative clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws). -/
def compactProductRealizationOutputRepresentativeLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k)) (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (L : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
      (wK : Scheme.FixedEtaleOriginWitness X P.Coefficient K)
      (wL : Scheme.FixedEtaleOriginWitness Y P.Coefficient L),
      P.CompactProductInput X wK.complex.obj → P.CompactProductInput Y wL.complex.obj →
      ∃ F : DerivedCategory.Plus
        (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)),
        Nonempty (F.obj ≅ externalProduct (ModuleCat.{u + 1} P.Coefficient) f g
          wK.complex.obj wL.complex.obj)

/-- The naturality clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws). -/
def compactProductRealizationNaturalityLawGeneral
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    (input : (X : Scheme.{u}) →
      ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))) :
    Prop :=
  ∀ {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (c : Compactification f) (d : Compactification g)
      (K K' : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
      (L L' : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)))
      (wK : Scheme.FixedEtaleOriginWitness X A K)
      (wK' : Scheme.FixedEtaleOriginWitness X A K')
      (wL : Scheme.FixedEtaleOriginWitness Y A L)
      (wL' : Scheme.FixedEtaleOriginWitness Y A L')
      (F F' : DerivedCategory.Plus
        (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} A)))
      (eF : F.obj ≅ externalProduct (ModuleCat.{u + 1} A) f g
        wK.complex.obj wL.complex.obj)
      (eF' : F'.obj ≅ externalProduct (ModuleCat.{u + 1} A) f g
        wK'.complex.obj wL'.complex.obj)
      (α : K.obj ⟶ K'.obj) (β : L.obj ⟶ L'.obj),
      input X wK.complex.obj → input X wK'.complex.obj →
      input Y wL.complex.obj → input Y wL'.complex.obj →
      tensorHom ((compactProductProSections A c).map α)
          ((compactProductProSections A d).map β) ≫
        compactProductProMap A c d K' L' wK' wL' F' eF' =
      compactProductProMap A c d K L wK wL F eF ≫
        (compactProductProSections A (compactProductCompactification c d)).map
          (compactProductProExternalMap A f g α β)

/-- Specialize the preceding universally quantified law to the actual finite datum
and its recorded finite-Tor constructible input predicate.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws). -/
def compactProductRealizationNaturalityLaw (P : PurityFiniteSetting.{u}) : Prop :=
  letI : Finite P.Coefficient :=
    letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  compactProductRealizationNaturalityLawGeneral P.Coefficient P.field.k P.CompactProductInput

/-- The compact kunneth clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws). -/
def compactProductRealizationCompactKunnethLaw (P : PurityFiniteSetting.{u}) : Prop :=
  letI : Finite P.Coefficient :=
    letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k))
    (g : Y ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    IsSeparated g → LocallyOfFiniteType g → QuasiCompact g →
    ∀ (c : Compactification f) (d : Compactification g)
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (L : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} P.Coefficient)))
      (wK : Scheme.FixedEtaleOriginWitness X P.Coefficient K)
      (wL : Scheme.FixedEtaleOriginWitness Y P.Coefficient L)
      (F : DerivedCategory.Plus
        (Sheaf (pullback f g).smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)))
      (eF : F.obj ≅ externalProduct (ModuleCat.{u + 1} P.Coefficient) f g
        wK.complex.obj wL.complex.obj),
      P.CompactProductInput X wK.complex.obj → P.CompactProductInput Y wL.complex.obj →
      IsIso (compactProductProMap P.Coefficient c d K L wK wL F eF)

/-- The proper support comparison clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-core-laws). -/
def compactProductRealizationProperSupportComparisonLaw (P : PurityFiniteSetting.{u}) : Prop :=
  letI : Finite P.Coefficient :=
    letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
      P.coefficients.l P.extension P.level P.level_pos
    inferInstanceAs (Finite (ULift.{u + 1} P.Ring))
  ∀ {X Z : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    ∀ (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (w : Scheme.FixedEtaleOriginWitness X P.Coefficient K),
      P.CompactProductInput X w.complex.obj →
      ∃ h : IsIso (compactProductSupportWitness P.Coefficient i K w),
        compactProductSupportWitness P.Coefficient i K w ≫
          compactProductProSupportMap P.Coefficient c i K w h =
        compactSupportFromProperSupport P.Coefficient c i w.complex.obj ≫
          (compactProductWitnessComparison P.Coefficient c K w).hom


end WeilConjectures.PurityFiniteSetting
