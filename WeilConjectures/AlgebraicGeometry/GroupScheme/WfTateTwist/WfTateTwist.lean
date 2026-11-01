/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Supporting.PbcWeilCategory
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.SmoothPurity.FrobeniusCoefficientTwists.FrobeniusCoefficientTwistsCanonical
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Weil.WeilTensorProduct
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import WeilConjectures.AlgebraicGeometry.Localized.LocalizedTStructure
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedTensorReflector
public import WeilConjectures.AlgebraicGeometry.Picard.SiteDerivedTensorDescentIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.ProperBaseChange.RingedKoszulCompletionReflector
public import WeilConjectures.ProperBaseChange.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
public import WeilConjectures.CategoryTheory.Ringed.RingedInternalHomDerivedComplete
public import WeilConjectures.CategoryTheory.Ringed.RingedPresentationTransport
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.HasLimits
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingMap
import WeilConjectures.SmoothPurity.CompletedCoefficientNormalization.CompletedCoefficientTensorNormalization
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteTowerLimit
import WeilConjectures.AlgebraicGeometry.Pur.PurRootTowerPreservation
import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement

/-! # Tate twists in the raw rational Weil category

Source: main-20261015, sec-algebraic-groups-lie-algebras/sk-d-ab-cyclotomic,
Definition of Tate twists (blueprint: def-wf-tate-twist).

The signed lines and their root-normalized transport are the existing constructions.
This module transports them through the canonical completed coefficient isomorphism
and restricts their tensor action to the actual PBC integral and rational categories.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures.WfTateTwist

variable (D : FiniteFieldDatum.{u}) (c : D.CoefficientDatum)
  (X₀ : Over (Spec (CommRingCat.of D.k₀)))
  [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

variable (E : Padic.FiniteCoefficientFields c.l c.Qbar)

/-- The existing completed coefficient module category, with its fixed small-site size.
Source: definition, completed coefficients (blueprint: def-wf-tate-twist). -/
abbrev Modules := pbcModules (D.geometricFiber X₀).left
  (pbcAdicCompletion (D.geometricFiber X₀).left (pbcStageDatum.{u} c.l c.Qbar E))

/-- The published signed line, in the PBC coefficient coordinates.
Source: definition, E(0), E(m), and E(-m) (blueprint: def-wf-tate-twist). -/
abbrev line (m : ℤ) : Modules D c X₀ E :=
  pbcTateLineSheaf c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- Exact transport on completed module sheaves along geometric Frobenius.
Source: definition, P_E (blueprint: def-wf-tate-twist). -/
abbrev pull := pbcIsoModulePullback (D.geometricFrobenius X₀).hom
  (pbcStageDatum.{u} c.l c.Qbar E)

/-- Insertion into the canonical module pullback, through its normalized adjunction unit.
Source: definition, inverse-image tensor comparison (blueprint: def-wf-tate-twist). -/
def sectionMap (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
    (x : M.val.obj (op V)) :=
  ((proEtaleRingModuleAdjunction (D.geometricFrobenius X₀).hom
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (pbcAdicCompletion _ (pbcStageDatum.{u} c.l c.Qbar E))
    (asIso (AlgebraicGeometry.Scheme.completedCoefficientMap (D.geometricFrobenius X₀).hom
      (pbcStageDatum.{u} c.l c.Qbar E)))).unit.app M).val.app (op V) x

/-- Exact sheaf tensor with the existing signed line.
Source: definition, K(m) (blueprint: def-wf-tate-twist). -/
abbrev tensor (m : ℤ) :=
  pbcTateSheafTensor c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m

/-- The unique ordinary tensor/pullback comparison, followed by the root-line map.
The formula tests every module, every local section and every signed-line section;
thus it fixes the entire natural isomorphism, including the negative exponents.
Source: definition, induced tensor Weil map (blueprint: def-wf-tate-twist).
Proof: the module pullback tensor comparison sends a pulled pure tensor x tensor y
to pulled x tensor pulled y. Compose the second factor with lineMap. The coefficient
isomorphism preserves balancing. These formulas give inverse maps by inverse transport
and the inverse line map. They are natural in the input module. Local pure tensors
generate after sheafification, and adjunction-unit sections generate pullback, so the
formula determines the comparison uniquely. -/
theorem tensorComparison_exists (m : ℤ) :
    ∃! g : tensor D c X₀ E m ⋙ pull D c X₀ E ≅
        pull D c X₀ E ⋙ tensor D c X₀ E m,
      ∀ (M : Modules D c X₀ E) (V : (D.geometricFiber X₀).left.ProEt)
        (x : M.val.obj (op V)) (y : (line D c X₀ E m).val.obj (op V)),
        HEq ((g.hom.app M).val.app (op ((proEtaleBaseChange
          (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E ((tensor D c X₀ E m).obj M) V
              (SheafOfModules.siteSheafTensorTmul
                ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left).obj M)
                (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
                  (D.geometricFiber X₀).left m) (op V) x y)))
          (SheafOfModules.siteSheafTensorTmul
            ((purOrdinaryCoefficientModel c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left).obj ((pull D c X₀ E).obj M))
            (FrobeniusCoefficientTwists.line c.l (pbcFiniteField.{u} c.l c.Qbar E)
              (D.geometricFiber X₀).left m)
            (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
            (sectionMap D c X₀ E M V x)
            ((lineMap D c X₀ E m).hom.val.app
              (op ((proEtaleBaseChange (D.geometricFrobenius X₀).hom).obj V))
              (sectionMap D c X₀ E (line D c X₀ E m) V y))) := by
  sorry

/-- The ordinary comparison with its unique pure-tensor normalization.
Source: definition, tensor Frobenius map (blueprint: def-wf-tate-twist). -/
def tensorComparison (m : ℤ) := (tensorComparison_exists D c X₀ E m).exists.choose

/-- Exact descent of the ordinary tensor/pullback comparison to the derived category.
Source: definition, completed derived tensor with a line (blueprint: def-wf-tate-twist). -/
def ambientComparison (m : ℤ) :
    (tensor D c X₀ E m).mapDerivedCategory ⋙ (pull D c X₀ E).mapDerivedCategory ≅
      (pull D c X₀ E).mapDerivedCategory ⋙ (tensor D c X₀ E m).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (tensorComparison D c X₀ E m) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Restriction of the actual exact line tensor to the integral coefficient category.
Source: definition, integral representatives (blueprint: def-wf-tate-twist). -/
def integral (m : ℤ) :=
  pbcConditionalIntegral (pbcStageDatum.{u} c.l c.Qbar E)
    (pbcTateAmbient c.l (D.geometricFiber X₀).left (pbcFiniteField.{u} c.l c.Qbar E) m)
    (pbcTateAmbient_mem c.l (D.geometricFiber X₀).left
      (pbcFiniteField.{u} c.l c.Qbar E)
      (weilGeometricFiber_coefficientHypotheses D c X₀).2.1 m)

/-- The existing rational twist, with the geometric hypotheses supplied by finite type.
Source: definition, raw rationalization of K(m) (blueprint: def-wf-tate-twist). -/
def rational (m : ℤ) :=
  letI : Fact (∃ n : ℕ, topologicalKrullDim (D.geometricFiber X₀).left ≤ n) :=
    ⟨(weilGeometricFiber_coefficientHypotheses D c X₀).2.1⟩
  pbcTateRational c.l (D.geometricFiber X₀).left c.Qbar E m

end WeilConjectures.WfTateTwist
