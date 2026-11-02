/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection
public import WeilConjectures.EtaleCohomology.Purity.Smooth.CohomologicallySmooth
public import WeilConjectures.SixFunctors.Etale.Derived.Identity
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteExceptionalComposition
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekInvertible
public import WeilConjectures.SixFunctors.Etale.Derived.InvertiblePullback

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.ExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitudeProEtaleModule
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.Sf.SfFiniteExceptionalInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleUpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekProjection
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportProjectionApplication
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicTorAmplitudeTransport
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.HomCongr
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.SixFunctors.Supporting.PullbackTorAmplitude
import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientFlatModel
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.AlgebraicGeometry.Finite.FiniteTensorConstructibleCohomology
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleProEtale
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.HomCongr
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-!
# Exceptional co-projection for invertible tensor factors

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/
sec-poincare-duality/sec-the-trace-map-in-top-degree/sk-cor-trace/sk-thm-regular/
sk-thm-regular.proof.md, Step 4(iii), with the projection/counit construction of
sk-lem-coprojection and the exceptional compositor of sk-prop-sp-composition.
(blueprint: lem-pur-exceptional-invertible-tensor-composition).

The maps and equations are written in the canonical finite etale-origin coordinates.
The fully faithful comparison, with its tensor, pullback, compact-support and counit
comparisons, transports these equations to the small pro-etale constructible category.
In particular, no right adjoint on the ambient pro-etale derived category is used.
The law predicates below expand to equations of the specified maps, not existence
of unspecified isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Y Z : Scheme.{u}}
  (f : X ⟶ Y) (g : Y ⟶ Z)
  [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]

/-- Theta is the specified tensor/counit transpose, in pullback-first order.
Source: sk-thm-regular Step 4(iii), the tensor map of def-pur-co-smoothness.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalTensorTheta
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj (dualizingComplex Λ f) ⟶
        (R(f)^![Λ]).obj K :=
  (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).hom.app
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).app (dualizingComplex Λ f)) ≫
    dualizingComplexTensorMap Λ f K

/-- The specified action r_w = theta composed with 1 tensor w.
There is no smoothness assumption and w need not be invertible.
Source: sk-thm-regular, Step 4(iii), projection/counit tensor passage.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalCoefficientAction
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (J : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (w : J ⟶ dualizingComplex Λ f) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj J ⟶ (R(f)^![Λ]).obj K :=
  derivedTensorHom (ModuleCat.{u + 1} Λ)
    (𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) w ≫ exceptionalTensorTheta Λ f K

/-- The canonical shuffle chi: pullback-tensor, associators and the signed symmetry.
Source: sk-thm-regular, Step 4(iii), projection/counit tensor passage.
(blueprint: lem-pur-exceptional-invertible-tensor-composition). -/
def exceptionalCoefficientShuffle
    (K L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (J :
      _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (((L((f)^*[ModuleCat.{u + 1} Λ])).obj
      ((((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj (K)).obj (L)))))).obj (J)) ≅ (((derivedTensor
      (ModuleCat.{u + 1} Λ) X).obj ((((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
      (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))).obj (J)))).obj (((L((f)^*[ModuleCat.{u + 1}
      Λ])).obj (L)))) :=
  ((derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj J).mapIso (leftDerivedUpperStarTensorIso
      (ModuleCat.{u + 1} Λ) (f) (K) (L)) ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} Λ) X (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))
      (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (L))) (J)) ≪≫
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))).mapIso
      (((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) X).app (((L((f)^*[ModuleCat.{u + 1} Λ])).obj
      (L)))).app J) ≪≫
    (derivedTensorAssociator (ModuleCat.{u + 1} Λ) X (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (K)))
      (J) (((L((f)^*[ModuleCat.{u + 1} Λ])).obj (L)))).symm

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

open Etale

end AlgebraicGeometry.ProEtale
