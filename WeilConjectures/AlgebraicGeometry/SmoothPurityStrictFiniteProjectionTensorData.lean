/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityStrictCompactificationComparisonData
import WeilConjectures.AlgebraicGeometry.ProEtaleIntrinsicSectionCoordinates
import WeilConjectures.SixFunctors.FiniteTensorTotalComparison
import WeilConjectures.SixFunctors.FiniteTensorDerivedComparison
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! Tensor realization and representative data for strict finite projection words. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerShriek

private instance (priority := 20000) finiteRingSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  integralCoefficientRingSheafify.{u, u} T

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The canonical finite tensor realization and its pinned representative data.
Source: blueprint operations proof (2), finite tensor realization.
(blueprint: new-lem-sp-strict-finite-projection-tensor-data).

Proof: construct the prescribed identity-section realization with the additive
sheafification counit as its underlying comparison. Restrict the existing
semilinear tensor model to resolving pairs and descend the total comparison
through the localization. The two comparison theorems for total and derived
tensor supply the displayed tensor family and the pure-summand and
representative equations. The construction is uniform in the scheme and level.
-/
theorem strictFiniteProjectionTensorData (b : Base l E) :
    ∃ tensor : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ comparisonFiniteRealization l E b T n ≅
        ((comparisonFiniteRealization l E b T n).prod
          (comparisonFiniteRealization l E b T n)) ⋙
            comparisonLevelTensor l E b T n,
      (∀ (T : Scheme.{u}) (n : ℕ),
        ∃ e : SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
            (ULift.{u + 1, u} (R l E n)) T (B l E T n)
            (comparisonFiniteConstantSection l E T n),
        ∃ t : AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u}
            (B l E T n),
        ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
            (ULift.{u + 1, u} (R l E n)) T ⋙ e.derived ≅
              (e.derived.prod e.derived) ⋙ t.functor,
          HEq e.equivalence (sfIntrinsicModuleEquivalence T (R l E n)) ∧
          HEq e.underlying (comparisonFiniteUnderlying l E b T n) ∧
          HEq t.functor (comparisonLevelTensor l E b T n) ∧
          ComparisonFiniteTensorRepresentative l E b T n t ∧ HEq d (tensor T n) ∧
          Nonempty (@SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
            (ULift.{u + 1, u} (R l E n)) _ _ T (B l E T n)
            (comparisonFiniteConstantSection l E T n) e t d)) := by
  let e : ∀ (T : Scheme.{u}) (n : ℕ),
      SheafOfModules.OpenTensorNormalization.FiniteRealization.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n) := fun T n ↦ {
    equivalence := sfIntrinsicModuleEquivalence T (R l E n)
    underlying := comparisonFiniteUnderlying l E b T n
    scalar := by
      intro M W a x
      let U := sfRealizationUnit (R l E n) T M
      let H := (comparisonFiniteUnderlying l E b T n).hom.app M
      have hu (y : M.obj.obj W) : H.hom.app W (U.app W y) = y := by
        have h := (sheafificationAdjunction (Scheme.ProEt.topology T)
          AddCommGrpCat.{u + 1}).right_triangle_components
            ((sheafCompose (Scheme.ProEt.topology T)
              (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1, u} (R l E n)))
                AddCommGrpCat.{u + 1})).obj M)
        exact ConcreteCategory.congr_hom (congr_app h W) y
      obtain ⟨y, rfl⟩ := (sfRealizationSectionEquiv (R l E n) T M W).surjective x
      have hs := (U.app W).hom.map_smul a y
      have hh := congrArg (fun z ↦ H.hom.app W z) hs
      rw [hu] at hh
      calc
        _ = a • y := hh.symm
        _ = _ := by
          change a • y = a • (show M.obj.obj W from H.hom.app W (U.app W y))
          rw [hu] }
  classical
  let inc := fun (T : Scheme.{u}) (n : ℕ) ↦ ObjectProperty.ιOfLE
    (fun P (h : AlgebraicGeometry.Scheme.ProjectionRestriction.resolving (B l E T n) P) ↦
      (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mpr h.1)
  let t : ∀ (T : Scheme.{u}) (n : ℕ),
      AlgebraicGeometry.Scheme.ProjectionRestriction.TensorModel.{u} (B l E T n) :=
    fun T n ↦ {
      preadditive := by infer_instance
      functor := comparisonLevelTensor l E b T n
      representative := Functor.isoWhiskerLeft ((inc T n).prod (inc T n))
        ((b.calculus T).levelTensorModels n).comparison
      descent := by
        intro F G
        obtain ⟨_, _, _, hdesc⟩ := SheafOfModules.cochain_tensor_model_rigidity
          (Scheme.ProEt.topology T) (B l E T n)
        have hp : AlgebraicGeometry.Scheme.ProjectionRestriction.resolving (B l E T n) =
            SheafOfModules.cochainTensorFlatRepresentatives
              (Scheme.ProEt.topology T) (B l E T n) := by
          funext P
          apply propext
          dsimp only [AlgebraicGeometry.Scheme.ProjectionRestriction.resolving,
            SheafOfModules.cochainTensorFlatRepresentatives]
          exact and_congr
            (CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).symm Iff.rfl
        rw [hp]
        simpa only [SheafOfModules.cochainTensorRepresentativeLocalization] using
          hdesc (AlgebraicGeometry.Scheme.ProjectionRestriction.Der
            (B l E T n)) inferInstance F G }
  have hrep (T : Scheme.{u}) (n : ℕ) :
      ComparisonFiniteTensorRepresentative l E b T n (t T n) := by
    intro P Q hp hq hp' hq'
    exact HEq.rfl
  have hd (T : Scheme.{u}) (n : ℕ) :
      ∃ d : SheafOfModules.OpenTensorNormalization.finiteTensor.{u}
          (ULift.{u + 1, u} (R l E n)) T ⋙ (e T n).derived ≅
            ((e T n).derived.prod (e T n).derived) ⋙ (t T n).functor,
        Nonempty (SheafOfModules.OpenTensorNormalization.FiniteTensorPin.{u}
          (e T n) (t T n) d) := by
    have : Presheaf.IsLocallySurjective (Scheme.ProEt.topology T)
        (comparisonFiniteConstantSection l E T n) := by
      dsimp [comparisonFiniteConstantSection]
      infer_instance
    obtain ⟨s, hs⟩ :=
      SheafOfModules.OpenTensorNormalization.finite_tensor_total_comparison_exists.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n) (e T n)
    obtain ⟨d, hd⟩ :=
      SheafOfModules.OpenTensorNormalization.finite_tensor_derived_comparison_exists.{u}
        (ULift.{u + 1, u} (R l E n)) T (B l E T n)
        (comparisonFiniteConstantSection l E T n) (e T n) s hs (t T n)
    exact ⟨d, ⟨SheafOfModules.OpenTensorNormalization.FiniteTensorPin.mk.{u}
      (fun P Q ↦ s.app (P, Q)) hs hd⟩⟩
  choose d hd using hd
  refine ⟨d, ?_⟩
  intro T n
  exact ⟨e T n, t T n, d T n, HEq.rfl, HEq.rfl, HEq.rfl,
    hrep T n, HEq.rfl, hd T n⟩

end AlgebraicGeometry.ProEtale.SpTowerShriek
