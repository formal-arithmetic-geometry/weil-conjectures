/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralHomReductionModels
import all WeilConjectures.Algebra.Homology.ScalarTensorComparisonTransport
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Derived tensor comparison component for integral reduction

This isolates the comparison-isomorphism field required by
`ReductionPresentation`.
(blueprint: lem-sf-integral-hom-reduction-normalization).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe d t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace WeilConjectures.IntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : AlgebraicGeometry.Scheme.{t}) (D : FiniteFieldDatum.{d}) (hl : l ≠ D.p)

private noncomputable def tensorModelIso
    [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)}]
    [(AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)}]
    (R : Sheaf (AlgebraicGeometry.Scheme.ProEt.topology Y) CommRingCat.{max u (t + 1)})
    (a : TensorPresentation.{t, u} Y R)
    (S : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{t + 1, t, u, (max u (t + 1)) + 1}
        (AlgebraicGeometry.Scheme.ProEt.topology Y) R))
    (T : CoefficientTensorModels.{u, t + 1, t, (max u (t + 1)) + 1}
      (AlgebraicGeometry.Scheme.ProEt.topology Y) R S) : a.tensor ≅ S.tensor := by
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let i := coefficientKFlatInclusion.{u, t + 1, t} J R
  let L := i ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (Modules.{t, u} Y R) (.up ℤ)).inverseImage i
  letI := RingedDerivedNative.kFlatLocalization.{t + 1, t, u, (max u (t + 1)) + 1} J R
  -- Both tensor models compute the same total tensor on K-flat representatives.
  let e : (L.prod L) ⋙ a.tensor ≅ (L.prod L) ⋙ S.tensor :=
    a.representative.symm ≪≫ T.comparison
  -- Restriction along the product localization is fully faithful.
  exact (Localization.fullyFaithfulWhiskeringLeft (L.prod L) (W.prod W)
    (Derived.{t, u} Y R)).preimageIso e

/-- The derived tensor comparison is available for any fixed finite target.

Source: Stacks Tag 07A4; blueprint order 2478, proof step 3.
Proof: extend both factors to the finite coefficient sheaf on K-flat
representatives. Balanced tensor associativity gives mutually inverse maps;
deriving this comparison yields the displayed natural isomorphism.
-/
theorem reduction_comparison_exists
    (a : TensorPresentation.{t, u} Y
      (completedIntegralCommRingSheaf l E Y D hl)) (n : ℕ)
    (target : TensorPresentation.{t, u} Y
      (integralCoefficientCommRingSheaf l E Y n)) :
    Nonempty (a.tensor ⋙ integralDerivedReduction l E Y D hl n ≅
      ((integralDerivedReduction l E Y D hl n).prod
        (integralDerivedReduction l E Y D hl n)) ⋙ target.tensor) := by
  classical
  let : EssentiallySmall.{t + 1} Y.ProEt := essentiallySmallSelf.{0, t, t + 1} _
  let : HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology Y)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify.{t, u} Y
  let : (AlgebraicGeometry.Scheme.ProEt.topology Y).WEqualsLocallyBijective
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbLocallyBijective.{t, u} Y
  let J := AlgebraicGeometry.Scheme.ProEt.topology Y
  let c := completedIntegralCommRingProjection l E Y D hl n
  let : ∀ R : Sheaf J CommRingCat.{max u (t + 1)},
      HasDerivedCategory.{(max u (t + 1)) + 1}
        (SheafOfModules.scalarModules.{t + 1, t, max u (t + 1)} J R) :=
    fun R ↦ HasDerivedCategory.standard _
  obtain ⟨M, μ, _⟩ :=
    scalarInternalHomAdjunction_exists.{t + 1, t, u, (max u (t + 1)) + 1} (J := J)
  let hobj := (integralReductionExistence l E Y D hl n).choose_spec.choose
  have he := ScalarTensorTransport.extension_eq.{t + 1, t, u, (max u (t + 1)) + 1}
    J c (M.scalar c) (integralReductionChangeOfRings l E Y D hl n) hobj
    (integralReductionExistence l E Y D hl n).choose_spec.choose_spec.choose
  obtain ⟨b⟩ :=
    ScalarTensorTransport.fixedScalarTensorComparison_exists.{t + 1, t, u,
      (max u (t + 1)) + 1} J c M (μ c)
      (integralReductionChangeOfRings l E Y D hl n) (reductionAdditive l E Y D hl n)
      hobj he (integralDerivedReduction l E Y D hl n)
      (integralDerivedReductionCounit l E Y D hl n)
      (by with_unfolding_all exact integralDerivedReductionUniversal l E Y D hl n)
  -- Conjugate the fixed scalar comparison by the two tensor-model identifications.
  let e := tensorModelIso Y _ a (M.closed _) (M.model _)
  let e' := tensorModelIso Y _ target (M.closed _) (M.model _)
  exact ⟨Functor.isoWhiskerRight e (integralDerivedReduction l E Y D hl n) ≪≫ b.iso ≪≫
    Functor.isoWhiskerLeft ((integralDerivedReduction l E Y D hl n).prod
      (integralDerivedReduction l E Y D hl n)) e'.symm⟩

end WeilConjectures.IntegralHom
