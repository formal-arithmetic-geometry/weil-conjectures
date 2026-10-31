/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientPairingChange.InternalAdjunctionPairingChange
import all WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarMonoidal
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.EtaleScalarNormalizations
import all WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import WeilConjectures.SixFunctors.Etale.Derived.Stability.HomDevissage
import WeilConjectures.SixFunctors.Etale.Derived.GenericFibre.Comparison

/-! Evaluation comparison for a locally projective coefficient sheaf. -/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Etale
open CoefficientPairingChange

attribute [local instance 2000] scalarSheafMonoidal

private theorem evaluation_iso_of_dual
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K N : DerivedCategoryModule A X)
    (D : DerivedCategoryModule A X) [ExactPairing D K] :
    IsIso (evaluationComparison φ X K N) := by
  classical
  let G := scalarExtension φ X
  let δ := ExceptionalCoefficients.tensorIso φ X
  have hc : IsEtaleHomTensorCanonical X φ (fun P Q ↦ (δ.app (P, Q)).symm) := by
    refine ⟨ExceptionalCoefficients.productIso_natural₁ _ _ _ δ,
      ExceptionalCoefficients.productIso_natural₂ _ _ _ δ, ?_⟩
    exact ExceptionalCoefficients.site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) X (ProEtale.etaleSheafExtendScalars φ X) G
      (scalarExtensionRepresentative φ X) δ
      (ExceptionalCoefficients.scalarExtension_normalizations φ X).2
  have he : etaleHomTensorComparison X φ = fun P Q ↦ (δ.app (P, Q)).symm :=
    (etaleHomTensorComparison_existsUnique X φ).unique
      (etaleHomTensorComparison_existsUnique X φ).choose_spec.1 hc
  obtain ⟨c, _, ht, _⟩ := ExceptionalCoefficients.scalarExtension_coreMonoidal A B φ X
  let := c.toMonoidal
  have hm (P Q : DerivedCategoryModule A X) :
      (etaleHomTensorComparison X φ P Q).hom = Functor.LaxMonoidal.μ G P Q := by
    rw [he]
    exact (congrArg Iso.inv (ht P Q)).symm
  have hv : evaluationComparison φ X K N =
      (Functor.LaxMonoidal.ihomComparison G K).natTrans.app N := by
    unfold evaluationComparison
    rw [hm, Functor.LaxMonoidal.ihomComparison_app_eq_curry]
    rfl
  rw [hv]
  exact Functor.Monoidal.isIso_ihomComparison_app_of_exactPairing G D K N

/-- The evaluation comparison is an isomorphism for a locally finite-projective sheaf.
Source: the finite-projective dual calculation in paragraph 3 of
`thm-coef-finite-hom`.

The finite projective local values make the sheaf finite locally constant and flat,
by the finite-value and geometric-stalk criteria. Its degree-zero complex has a
left dual by the existing source theorem. Scalar extension is strong monoidal on
derived categories. Its transported tensorator satisfies the prescribed cochain
normalization, so uniqueness identifies it with the specified tensor comparison.
The evaluation transpose is its internal-Hom comparison and is invertible at this
left-dualizable first argument. No boundedness condition on the second argument is
needed for this step.
(blueprint: lem-coef-locally-projective-coefficient-hom-evaluation). -/
theorem locallyProjectiveCoefficientHom_evaluation
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (L : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hL : ∃ d : Scheme.LocallyConstantDatum L, ∀ i : d.cover.I₀,
      ∃ P : ModuleCat.{u + 1} A, Module.Finite A P ∧ Module.Projective A P ∧
        Nonempty (L.over (d.cover.etalePrecoverageToEtale i) ≅
          (constantSheaf (T.smallEtaleTopology.over (d.cover.etalePrecoverageToEtale i))
            (ModuleCat.{u + 1} A)).obj P))
    (N : DerivedCategoryModule A T)
    (_hN : DerivedCategory.isBoundedConstructible A T N ∧
      ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.hasTorAmplitudeIn A T a b N) :
    IsIso (evaluationComparison φ T ((_root_.DerivedCategory.singleFunctor _ 0).obj L) N) := by
  classical
  obtain ⟨d, hd⟩ := hL
  have hflc : Scheme.IsFiniteLocallyConstantSheaf L := by
    apply (Scheme.finite_locally_constant_module_values_iff L).1.mp
    refine ⟨d, fun i ↦ ?_⟩
    obtain ⟨P, hP, _, eP⟩ := hd i
    let : Module.Finite A P := hP
    exact ⟨P, Module.finite_of_finite A, eP⟩
  let : Scheme.IsFiniteLocallyConstantSheaf L := hflc
  have hflat : ObjectProperty.flat L := by
    apply (AlgebraicGeometry.Etale.flat_iff_forall_flat_sheafFiber_obj L).mpr
    intro Ω _ _ s
    have : Scheme.JointlySurjective Scheme.etalePrecoverage.{u} := by
      unfold Scheme.etalePrecoverage
      exact Scheme.instJointlySurjectivePrecoverage (P := @AlgebraicGeometry.Etale)
    obtain ⟨i, x, hx⟩ := d.cover.exists_eq (s default)
    have : Etale (d.cover.f i) := d.cover.map_prop i
    obtain ⟨t, ht, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
      (d.cover.f i) s x hx
    obtain ⟨P, _, hproj, ⟨eP⟩⟩ := hd i
    let : Module.Projective A P := hproj
    have e := Scheme.constantValueStalkIso L (d.cover.etalePrecoverageToEtale i) P eP t
    have hf : ObjectProperty.flat
        (((Scheme.pointSmallEtale (t ≫ d.cover.f i)).sheafFiber
          (A := ModuleCat.{u + 1} A)).obj L) := by
      apply ObjectProperty.prop_of_iso _ e.symm
      exact (ModuleCat.flat_iff_flat P).mpr (Module.Flat.of_projective (R := A))
    rw [ht] at hf
    exact ObjectProperty.prop_of_iso _
      (((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} A)).app L).symm hf
  obtain ⟨D, _, ⟨ep⟩⟩ :=
    exists_exactPairing_singleFunctor_of_isFiniteLocallyConstantSheaf A L hflat
  let := ep
  exact evaluation_iso_of_dual φ T _ N D

end AlgebraicGeometry.Etale
