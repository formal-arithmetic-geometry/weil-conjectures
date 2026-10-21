/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q73
-/
module

public import Sheaf.Paper.CompactProductRealizationCoreLaws
public import Sheaf.AlgebraicGeometry.CompactProductRealizationArrows
public import Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.AlgebraicGeometry.ProperSupportCompactMaps
public import Sheaf.AlgebraicGeometry.CompactProductArrows
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
public import Sheaf.AlgebraicGeometry.SupportSiteComparison
public import Sheaf.Paper.SupportedClassGeometry

/-! # Compact-product comparison laws for retained realizations

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
open AlgebraicGeometry AlgebraicGeometry.Etale


/-- The proper support square clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
def compactProductRealizationProperSupportSquareLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Y Z W : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k)) (g : Y ⟶ Spec (.of P.field.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Compactification f) (d : Compactification g)
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    [IsProper (i ≫ f)] [IsProper (j ≫ g)]
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
    ∃ (hK : IsIso (compactProductSupportWitness P.Coefficient i K wK))
      (hL : IsIso (compactProductSupportWitness P.Coefficient j L wL))
      (hF : IsIso (compactProductSupportWitness P.Coefficient
        (supportedProductImmersion f g i j)
        ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (pullback f
          g)).mapDerivedCategoryPlus.obj F)
        (compactProductCanonicalWitness P.Coefficient (pullback f g) F))),
      ProEtale.supportedExteriorProductOverField P.Coefficient P.field.k f g i j K.obj L.obj ≫
        (ProEtale.supportSections (supportedProductImmersion f g i j)
          P.Coefficient).rightDerivedFunctor.map (compactProductOutputIso P.Coefficient f g K L wK
          wL F eF).inv ≫
        compactProductProSupportMap P.Coefficient (compactProductCompactification c d)
          (supportedProductImmersion f g i j)
          ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) (pullback f
            g)).mapDerivedCategoryPlus.obj F)
          (compactProductCanonicalWitness P.Coefficient (pullback f g) F) hF =
      tensorHom (compactProductProSupportMap P.Coefficient c i K wK hK)
          (compactProductProSupportMap P.Coefficient d j L wL hL) ≫
        compactProductProMap P.Coefficient c d K L wK wL F eF ≫
        (compactProductProSections P.Coefficient (compactProductCompactification c d)).map
          (compactProductOutputIso P.Coefficient f g K L wK wL F eF).inv

/-- The unit counit normalization clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
def compactProductRealizationUnitCounitNormalizationLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (w : Scheme.FixedEtaleOriginWitness X P.Coefficient K),
    P.CompactProductInput X w.complex.obj →
    ∃ h : IsIso (compactProductSupportWitness P.Coefficient i K w),
      compactProductProSupportMap P.Coefficient c i K w h =
        proCompactSupportOverField P.Coefficient f c i K.obj

/-- The supported classes clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
def compactProductRealizationSupportedClassesLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (w : Scheme.FixedEtaleOriginWitness X P.Coefficient K) (a : ℤ)
    (α : ProCompactSupportClassHom P.Coefficient f i P.compactProductUnit (K.obj⟦a⟧)),
    P.CompactProductInput X w.complex.obj →
    proCompactSupportClassAdjoint P.Coefficient f i P.compactProductUnit (K.obj⟦a⟧) α ≫
      proCompactSupportOverField P.Coefficient f c i (K.obj⟦a⟧) =
    proCompactSupportClassImage P.Coefficient f c i P.compactProductUnit (K.obj⟦a⟧) α

/-- The excision clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
def compactProductRealizationExcisionLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}}
    (f : X ⟶ Spec (.of P.field.k))
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
    (w : Scheme.FixedEtaleOriginWitness X P.Coefficient K)
    (F : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology c.Z) (ModuleCat.{u + 1} P.Coefficient)))
    (e : (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      c.i).mapDerivedCategory.obj F.obj ≅ K.obj),
    P.CompactProductInput X w.complex.obj →
    ∃ h : IsIso (proCompactSupportExcision P.Coefficient f c i K.obj F.obj e),
      proCompactSupportOverField P.Coefficient f c i K.obj ≫
        proCompactSupportToExtension P.Coefficient f c K.obj F.obj e =
      @inv _ _ _ _ (proCompactSupportExcision P.Coefficient f c i K.obj F.obj e) h ≫
        (ProEtale.compactProductForget P.Coefficient (i ≫ c.i)).app F.obj

/-- The witness independence clause, with the same quantified inputs and canonical maps.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
def compactProductRealizationWitnessIndependenceLaw (P : PurityFiniteSetting.{u}) : Prop :=
  ∀ {X Z : Scheme.{u}} (f : X ⟶ Spec (.of P.field.k)),
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f →
    ∀ (c : Compactification f) (i : Z ⟶ X) [IsClosedImmersion i] [IsProper (i ≫ f)]
      (K : DerivedCategory.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} P.Coefficient)))
      (w w' : Scheme.FixedEtaleOriginWitness X P.Coefficient K)
      (h : IsIso (compactProductSupportWitness P.Coefficient i K w))
      (h' : IsIso (compactProductSupportWitness P.Coefficient i K w')),
      P.CompactProductInput X w.complex.obj → P.CompactProductInput X w'.complex.obj →
      compactProductProSupportMap P.Coefficient c i K w h =
        compactProductProSupportMap P.Coefficient c i K w' h'

/-- The complete conjunction of the named universally quantified clauses above.
Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
projective-bundle-formula proof, Step 1
(blueprint: def-pur-compact-product-realization-laws). -/
structure CompactProductRealizationLaws (P : PurityFiniteSetting.{u}) : Prop where
  output_representative : P.compactProductRealizationOutputRepresentativeLaw
  naturality : P.compactProductRealizationNaturalityLaw
  compact_kunneth : P.compactProductRealizationCompactKunnethLaw
  proper_support_comparison : P.compactProductRealizationProperSupportComparisonLaw
  proper_support_square : P.compactProductRealizationProperSupportSquareLaw
  unit_counit_normalization : P.compactProductRealizationUnitCounitNormalizationLaw
  supported_classes : P.compactProductRealizationSupportedClassesLaw
  excision : P.compactProductRealizationExcisionLaw
  witness_independence : P.compactProductRealizationWitnessIndependenceLaw

end WeilConjectures.PurityFiniteSetting
