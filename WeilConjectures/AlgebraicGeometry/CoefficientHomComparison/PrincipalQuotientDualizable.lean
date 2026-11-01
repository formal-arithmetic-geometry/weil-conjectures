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
import all WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact
import WeilConjectures.CategoryTheory.Monoidal.Dualizable

/-! # Dualizability of the native finite coefficient object -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.CoefficientHomComparison

/-- The positive finite quotient is a dualizable object of the native integral
ordinary derived category.
Source: the derived Nakayama resolution; Stacks 08JD, 08JJ.
Proof: the non-zero-divisor power has an exact two-term free resolution.
Its cone has only two nonzero terms, each the tensor unit, and hence has
termwise duals. Bounded dualizable complexes remain dualizable under derived
localization. The cone augmentation is a quasi-isomorphism to the quotient,
so transport its dual along that isomorphism.
(blueprint: lem-per-principal-quotient-dualizable). -/
theorem principal_quotient_dualizable (X : Scheme.{u})
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    IsDualizable ((DerivedCategory.singleFunctor
      (AdicCompletion.Modules ℓ (ULift.{u} E.val) X) 0).obj
        (AdicCompletion.finiteModule ℓ (ULift.{u} E.val) X n)) := by
  let A := AdicCompletion.Modules ℓ (ULift.{u} E.val) X
  obtain ⟨d, hd, _⟩ := DerivedNakayama.derived_nakayama_resolution ℓ (ULift.{u} E.val)
  obtain ⟨w, hw⟩ := PrincipalNormalization.coefficient_exact ℓ (ULift.{u} E.val) X d hd n
  let s := ShortComplex.mk _ _ w
  let T := s.map (HomologicalComplex.single A (.up ℤ) 0)
  let P := CochainComplex.mappingCone T.f
  have hzero (j : ℤ) (hj : j ≠ 0) : IsZero (T.X₁.X j) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j hj
  have hzero' (j : ℤ) (hj : j ≠ 0) : IsZero (T.X₂.X j) :=
    HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ j hj
  have hsingle (j : ℤ) : IsDualizable (T.X₁.X j) := by
    by_cases hj : j = 0
    · subst j
      exact isDualizable_unit.of_iso
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ A)).symm
    · exact CategoryTheory.IsZero.isDualizable (hzero j hj)
  have hsingle' (j : ℤ) : IsDualizable (T.X₂.X j) := by
    exact hsingle j
  have : P.IsStrictlyGE (-1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff T.f i).2
      ⟨hzero (i + 1) (by omega), hzero' i (by omega)⟩
  have : P.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (CochainComplex.mappingCone.isZero_X_iff T.f i).2
      ⟨hzero (i + 1) (by omega), hzero' i (by omega)⟩
  have hp := DerivedCategory.isDualizable_Q_obj P (-1) 0 (fun j ↦
    ((hsingle (j + 1)).biprod (hsingle' j)).of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod T.f j (j + 1) rfl).symm)
  have := CochainComplex.mappingCone.quasiIso_descShortComplex
    (hw.map_of_exact (HomologicalComplex.single A (.up ℤ) 0))
  exact hp.of_iso (asIso (DerivedCategory.Q.map
    (CochainComplex.mappingCone.descShortComplex T)))

end AlgebraicGeometry.ProEtale.CoefficientHomComparison
