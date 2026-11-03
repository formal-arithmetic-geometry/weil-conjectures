/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Internal.InternalSignedTateTwist
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.Triangulated.LocalizingDetermination
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Integral.IntegralConstructibleCompactness
import WeilConjectures.AlgebraicGeometry.Integral.Proper.IntegralProperDirectSums
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralExtHomContinuity
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralStratumHomFormula
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.CategoryTheory.SixFunctors.ModuleObjects
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.AlgebraicGeometry.SixFunctors.QcqsIntegralFiniteModelCompleteness
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.AlgebraicGeometry.PrincipalTensorScalarExtension
import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteQuotientSupportedClassicalWindow
import WeilConjectures.SixFunctors.IntegralDualTorsionHeartSections
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Smooth purity with finite rational coefficients

Source: current blueprint, part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-coefficient-fields/sk-prop-sp-rational,
current proposition and proof (blueprint: sk-prop-sp-rational).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.SmoothPurityRational

variable (l : ℕ) [Fact l.Prime] (E : PadicAlgCl.FiniteIntermediateField l)

/-- The ambient right-hand functor in smooth purity: inverse image, the specified
rational Tate twist, and the cohomological shift.  The coefficient ring is the
continuous-function condensed ring attached to `E`.
Source: the right side of the displayed adjunction (blueprint: sk-prop-sp-rational). -/
def ambientRight {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) (d : ℕ) :
    DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.1) Y.left)) ⥤
      DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj (Profinite.continuousMapRingObj E.1) X.left)) :=
  (CondensedRing.upperStar (Profinite.continuousMapRingObj E.1) f.left).mapDerivedCategory ⋙
    tensorRight ((DerivedCategory.singleFunctor _ 0).obj
      (spInternalSignedTwist X.left _ (spRationalTwist X.left l E) (d : ℤ))) ⋙
      shiftFunctor _ (2 * (d : ℤ))

/-- The functor `f^*(-)(d)[2d]` restricted to bounded constructible complexes,
with its preservation witness supplied explicitly.
Source: twisted-pullback side of the adjunction (blueprint: sk-prop-sp-rational). -/
def right {k : Type u} [Field k] {X Y : Over (Spec (.of k))}
    (f : X ⟶ Y) (d : ℕ)
    (h : ∀ K : ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Y.left,
      constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left
        ((ambientRight l E f d).obj K.obj)) :
    ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Y.left ⥤
      ConstantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) X.left :=
  ObjectProperty.lift _
    ((constantModelBoundedConstructible (Profinite.continuousMapRingObj E.1) Y.left).ι ⋙
      ambientRight l E f d) h

end AlgebraicGeometry.ProEtale.SmoothPurityRational
