/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.InternalScalarTensorComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsPull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.ExtendScalarsMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleObjectRingedComparison.ModuleObjectRingedSiteDerivedComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.CoefficientHomCoefficientIso
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization

/-! # Integral descent in the specified spectral coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- Every bounded constructible finite-extension complex has a spectral integral model.
Source: Bhatt--Scholze Lemma 6.8.13 and Proposition 6.8.14(2); Step 5 of
lem-per-constructible-coefficient-hom-comparison.
Proof: the adic predicate comparison identifies finite constant constructibility with
the ordinary bounded constructibility predicate. Rationalization of the embedded
integral category is equivalent to the rational category, and rationalization has the
same objects. Essential surjectivity therefore supplies an embedded integral model.
Transport that model along integralIso to the spectral ring; coefficient isomorphism
transport preserves finite constant constructibility. The canonical scalar tower,
together with integralIso.hom followed by integralToField being the original inclusion,
identifies its scalar extension with the given rational complex.
(blueprint: lem-per-constructible-coefficient-integral-descent). -/
theorem constructible_coefficient_integral_descent
    (X : Scheme.{u}) [IsNoetherian X] (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (K : D X (Profinite.continuousMapRingObj.{u} E.val))
    (hK : bc X (Profinite.continuousMapRingObj E.val) K) :
    ∃ L : D X (integral.{u} ℓ E), bc X (integral ℓ E) L ∧
      Nonempty ((scalar X (integralToField ℓ E)).obj L ≅ K) := by
  classical
  let := PadicAlgCl.normedFieldOfAlgebra ℓ E.val
  let : NormedAlgebra ℚ_[ℓ] E.val :=
    { norm_smul_le c x := by
        change ‖algebraMap E.val (PadicAlgCl ℓ) (c • x)‖ ≤
          ‖c‖ * ‖algebraMap E.val (PadicAlgCl ℓ) x‖
        rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, norm_mul,
          PadicAlgCl.norm_extends] }
  have hK' : boundedConstructible (condensedRingObj
      (Profinite.continuousMapRingObj E.val) X) K := by
    rwa [(adicConstructibilityPredicateComparison ℓ X _
      (.continuous E.val)).2]
  let F := boundedConstructibleExtendScalars X ℓ E
  have : F.EssSurj := Functor.essSurj_of_iso (rationalizationQCompEquivalenceIso X ℓ E)
  let M := F.objPreimage ⟨K, hK'⟩
  have hM : bc X (Profinite.padicIntegersRingObj ℓ E.val) M.obj := by
    change constantModelBoundedConstructible (Profinite.padicIntegersRingObj ℓ E.val) X M.obj
    rw [← (adicConstructibilityPredicateComparison ℓ X _ (.integral E.val)).2]
    exact M.property
  refine ⟨(scalar X (integralIso ℓ E).hom).obj M.obj,
    coefficient_iso_preserves_bc X (integralIso ℓ E) M.obj hM, ⟨?_⟩⟩
  have hm : (integralIso ℓ E).hom ≫ integralToField ℓ E =
      padicIntegersRingObjToContinuousMapRingObj ℓ E := by
    simp only [integralToField, Iso.hom_inv_id_assoc]
  have hc : (scalar X (integralToField ℓ E)).obj
      ((scalar X (integralIso ℓ E).hom).obj M.obj) ≅
      (Mod.extendScalars (padicIntegersToPadicSubfield X ℓ E)).leftDerivedFunctor.obj
        M.obj := by
    exact (Mod.derivedExtendScalarsCompIso
      (coefficientMap (integralIso ℓ E).hom X) (coefficientMap (integralToField ℓ E) X)
      (padicIntegersToPadicSubfield X ℓ E) (by rw [← coefficientMap_comp, hm])).symm.app M.obj
  exact hc ≪≫ (boundedConstructible _).ι.mapIso (F.objObjPreimageIso ⟨K, hK'⟩)

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
