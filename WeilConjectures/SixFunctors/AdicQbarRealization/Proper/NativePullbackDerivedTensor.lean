/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackKFlat
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackExactCounits
import WeilConjectures.AlgebraicGeometry.TensorPullbackRepresentativeDescent
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
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
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
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

/-! # Descent of the normalized native tensor comparison

Source: Stacks Tags 07A4 and 04VK; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-derived-tensor)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- A native cochain tensor comparison descends uniquely to the specified ambient
closed tensor models, with the representative square on every K-flat pair.
Source: Stacks Tags 07A4 and 04VK; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-derived-tensor).

Proof: restrict cochain localization to all K-flat complexes; this restriction and
its product are localizations. Native pullback preserves that class. On the product
of those categories, compose the inverse source tensor model, the normalized pull
counit, the localized cochain comparison, the target tensor model and the inverses
of the two pull counits. All counits are invertible because native pullback is exact.
Full faithfulness of localization precomposition gives the unique derived comparison.
Cancelling the model and counit isomorphisms gives its stated representative square. -/
theorem nativePullbackDerivedTensor (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (C : At l Y S)
    (cochain : coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S) ⋙
        (ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ) ≅
      (((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ)).prod
        ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))) ⋙
          coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R)) :
    ∃! tensor : C.closed.tensor ⋙ ContinuousRational.derivedPull p O.coefficient ≅
        ((ContinuousRational.derivedPull p O.coefficient).prod
          (ContinuousRational.derivedPull p O.coefficient)) ⋙ A.closed.tensor,
      tensorRepresentative l p R S O A C cochain
        (fun P hP ↦ nativePullbackKFlat p O.coefficient P hP) tensor := by
  have := nativePullbackCoefficient_isIso l p R S O
  have he (P : CochainComplex (modules l Y S) ℤ) : IsIso (O.pullCounit.app P) :=
    nativePullbackNormalizedCounit_isIso p O.coefficient O.pullCounit O.pull_normalized P
  let PY : ObjectProperty (CochainComplex (modules l Y S) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology Y) (R := ring l Y S)
  let PX : ObjectProperty (CochainComplex (modules l X R) ℤ) :=
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := ring l X R)
  let q := PY.ι ⋙ DerivedCategory.Q
  let W := (HomologicalComplex.quasiIso (modules l Y S) (.up ℤ)).inverseImage PY.ι
  have : q.IsLocalization W := RingedDerivedNative.kFlatLocalization.{u + 1, u, u, u + 2}
    (ProEt.topology Y) (ring l Y S)
  let ff := Localization.fullyFaithfulWhiskeringLeft (q.prod q) (W.prod W)
    (DerivedCategory (modules l X R))
  exact tensorComparisonDescent DerivedCategory.Q DerivedCategory.Q
    ((ContinuousRational.modulePull p O.coefficient).mapHomologicalComplex (.up ℤ))
    (ContinuousRational.derivedPull p O.coefficient) O.pullCounit PY PX
    (fun P hP ↦ nativePullbackKFlat p O.coefficient P hP) ff
    (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology Y) (ring l Y S))
    (coefficientTotalTensor.{u + 1, u + 1, u} (ProEt.topology X) (ring l X R))
    C.closed.tensor A.closed.tensor C.models.comparison A.models.comparison cochain
    (fun P _ ↦ he P) (fun P Q _ _ ↦ he _)

end WeilConjectures.AdicQbarRealization.Proper
