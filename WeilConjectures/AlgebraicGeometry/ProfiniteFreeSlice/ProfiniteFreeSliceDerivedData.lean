/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.InternalBar.CondensedInternalBarResolution
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.AlgebraicGeometry.CoefficientHomRepresentativeEvaluation
import WeilConjectures.AlgebraicGeometry.ProfiniteFreeSlice.ProfiniteFreeSliceLocalizationData

/-! # The profinite free chain model and localization

Source: Stacks Project Tags 08FI, 08J7; HRS Section 3.
(blueprint: new-c1-profinite-free-slice-derived-data).

This module assembles the chain comparison and its normalized localization.
The representative and evaluation fields are inherited from the same chain model;
the localization field uses that model without choosing a second comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u

-- Avoid the universe-mismatched global instance exposed by newer imports.
attribute [local instance 20000] HasDerivedCategory.ofIsGrothendieckAbelian
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
open ModuleObjectRingedComparison WeilConjectures
attribute [local instance 1000001] sectionRingHasSheafCompose sectionModulesGrothendieck
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) (P : Profinite.{u})

/-- The chain model and localization data with their displayed normalizations.
(blueprint: new-c1-profinite-free-slice-derived-data). -/
structure DerivedComparisonData
    (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P)
    (homComparison : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) where
  gamma : (CondensedRing.derivedHom Λ X).obj (op (derivedFree Λ X P)) ≅
    sliceDerived Λ X P
  representative : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective],
    homComplex (R := ring Λ X) (sectionFreeComplex Λ X P) ((complexForward Λ X).obj J) ≅
      (complexForward Λ X).obj ((sliceComplex Λ X P).obj J)
  evaluation : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective]
      (n : ℤ) (V : X.ProEt)
      (φ : ((homComplex (R := ring Λ X) (sectionFreeComplex Λ X P)
        ((complexForward Λ X).obj J)).X n).val.obj (op V)),
    (((representative J).hom.f n).val.app (op V)) φ =
      (sectionToSlice Λ X P (J.X n) V).hom
        (evaluateHomSection Λ X P freeIso J n V φ)
  localization : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective]
      [CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J)],
    homComparison.hom.app (op (derivedFree Λ X P), DerivedCategory.Q.obj J) ≫
      (hom Λ X).map
        (X := (op ((forward Λ X).obj (derivedFree Λ X P)),
          (forward Λ X).obj (DerivedCategory.Q.obj J)))
        (Y := (op (DerivedCategory.Q.obj (sectionFreeComplex Λ X P)),
          DerivedCategory.Q.obj ((complexForward Λ X).obj J)))
        (Quiver.Hom.op ((localizationIso Λ X).inv.app (freeComplex Λ X P)),
          (localizationIso Λ X).hom.app J) ≫
      (WeilConjectures.coefficientHomResolutionIso.{u, u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (ring Λ X) (sectionFreeComplex Λ X P)
          ((complexForward Λ X).obj J)).hom =
      (forward Λ X).map (gamma.hom.app (DerivedCategory.Q.obj J)) ≫
        (forward Λ X).map (derivedSliceModel Λ X P J).hom ≫
        (localizationIso Λ X).hom.app ((sliceComplex Λ X P).obj J) ≫
        DerivedCategory.Q.map (representative J).inv ≫
        DerivedCategory.Q.map
          (((homComplexFunctor (R := ring Λ X)).obj (op (sectionFreeComplex Λ X P))).map
            ((CochainComplex.toKInjectiveResolution.{u + 1} (Modules Λ X)).app
              ((complexForward Λ X).obj J)))


/-- The K-injective chain model and its normalized derived localization.
Source: Stacks Project Tags 08FI and 08J7
(blueprint: new-c1-profinite-free-slice-derived-data).

Proof: exists_chain_comparison_data supplies the natural chain isomorphism,
its component evaluation formula, and chain-map naturality. Apply
exists_localized_chain_comparison with that exact chain model, the given
K-injective restriction assertion, and homComparison. It supplies gamma
and the specified localization equation. Insert these into the record,
restricting the chain model to K-injective inputs. The closed tensor
structure and evaluation normalization remain separate fields of the
parent Comparison; no additional choice or compatibility assumption is
needed for this assembly. -/
theorem exists_derived_comparison_data
    (freeIso : pulledFree Λ X P ≅ freeOnTest Λ X P)
    (hK : ∀ (J : CochainComplex (Internal Λ X) ℤ) [J.IsKInjective],
      CochainComplex.IsKInjective ((restrictionComplex Λ X P).obj J))
    (homComparison : Functor.uncurry.obj (CondensedRing.derivedHom Λ X) ⋙ forward Λ X ≅
      ((forward Λ X).op.prod (forward Λ X)) ⋙ hom Λ X) :
    Nonempty (DerivedComparisonData Λ X P freeIso homComparison) := by
  obtain ⟨d⟩ := exists_chain_comparison_data Λ X P freeIso
  obtain ⟨gamma, hgamma⟩ :=
    exists_localized_chain_comparison Λ X P freeIso d hK homComparison
  exact ⟨{
    gamma := gamma
    representative := fun J ↦ d.representative J
    evaluation := fun J ↦ d.evaluation J
    localization := hgamma
  }⟩

end AlgebraicGeometry.ProEtale.ProfiniteFreeSlice
