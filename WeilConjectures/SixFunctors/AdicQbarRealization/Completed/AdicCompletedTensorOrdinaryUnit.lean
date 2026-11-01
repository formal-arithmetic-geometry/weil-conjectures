/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Completed.AdicCompletedTensorFiniteModels
import WeilConjectures.SmoothPurity.Supporting.Coefficient.RegularCoefficientCoherentReduction
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement

/-! # The coefficient unit in ordinary native realization

Source: BS Lemma 6.8.2 and Remark 6.8.15; Stacks Tags 03EL, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization

private theorem testDatum (l : ℕ) : ∃ D : FiniteFieldDatum.{0}, l ≠ D.p := by
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let D : FiniteFieldDatum.{0} :=
    { p := p
      a := 1
      q := p
      prime := hp
      exponent_pos := le_rfl
      cardinality_eq := (pow_one p).symm
      k₀ := ZMod p
      card_base := by simp [Nat.card_eq_fintype_card]
      k := AlgebraicClosure (ZMod p) }
  refine ⟨D, ?_⟩
  change l ≠ p
  omega

private def ordinaryScalarUnit (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    (pbcExtend φ).obj
      (SheafOfModules.unit ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A)) ≅
    SheafOfModules.unit ((sheafCompose (ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B) :=
  eqToIso ((pbcExtensionExistence φ).choose_spec.choose _) ≪≫
    SheafOfModules.scalarExtensionUnitIso φ

private theorem regularKFlat (X : Scheme.{u})
    (A : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    CochainComplex.IsKFlatIndependentCoefficients (J := ProEt.topology X) (R := A)
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) A) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  intro F hF i
  exact (quasiIsoAt_iff_exactAt' (HomologicalComplex.rightUnitor F).hom i (hF i)).1
    inferInstance

private def derivedScalarUnit (X : Scheme.{u})
    {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :
    (pbcDerivedExtend φ).obj
      (DerivedCategory.Q.obj
        (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) A)) ≅
    DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) B) := by
  let P := ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) A
  have : IsIso (pbcComplexCounit φ P) := by
    have := pbcExtensionCounit_isIso φ P (regularKFlat X A)
    dsimp only [pbcComplexCounit]
    infer_instance
  exact asIso (pbcComplexCounit φ P) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (pbcExtend φ) (.up ℤ) 0).app _ ≪≫
        (CochainComplex.singleFunctor _ 0).mapIso (ordinaryScalarUnit X φ))

private theorem integralUnitRegular
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty ((pullbackTensorIntegralUnit l E X).obj ≅
      integralConstantCoefficientObject l E X) := by
  obtain ⟨D, hD⟩ := testDatum l
  let K : sfIntegralConstructibleCategory l E X :=
    ⟨integralConstantCoefficientObject l E X,
      (integralConstantCoefficient_constructible l E X D hD).2.1⟩
  let S := pullbackTensorCalculus l E X
  let F := (sfIntegralConstructible l E X).ι ⋙ S.reduction
  have : F.Full := (integralSystemReduction_fullyFaithful l E X).1
  have : F.Faithful := (integralSystemReduction_fullyFaithful l E X).2
  obtain ⟨e⟩ := regularCoefficient_coherentReduction l E X
  let c : F.obj (pullbackTensorIntegralUnit l E X) ≅ F.obj K :=
    pullbackTensorIntegralUnitReduction l E X ≪≫ e.symm
  exact ⟨(sfIntegralConstructible l E X).ι.mapIso (F.preimageIso c)⟩

/-- The ordinary image of the common-stage coefficient unit is the regular native
coefficient sheaf in degree zero. Source: BS Lemma 6.8.2 and Remark 6.8.15.
(blueprint: lem-sf-adic-completed-tensor-ordinary-unit).
Proof: coherent reduction is fully faithful on constructible complete objects.
Both the reconstructed integral tensor unit and the regular coefficient have the
coherent ring unit as reduction, so lift their comparison. Derived scalar extension
of the regular module is the target regular module: compute on its K-flat
single complex and use the sheafified scalar multiplication isomorphism. At the
least finite coefficient field, compose these identifications
with the inverse of the specified integral realization comparison. -/
theorem completedTensorOrdinaryUnit
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (R : LocallyFiniteAdicRealization.Realization l X)
    [∀ x : X, Invertible (l : X.residueField x)] :
    Nonempty (DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X) (ring l X R)) ≅
      (ordinary l X R).obj (pullbackTensorCommonUnit l (PadicAlgCl l) X)) := by
  let E := Padic.finiteCoefficientBase l (PadicAlgCl l)
  let K := pullbackTensorIntegralUnit l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  obtain ⟨e⟩ := integralUnitRegular l
    (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X
  let d : K.obj ≅ DerivedCategory.Q.obj
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology X)
        (completedIntegralCommRingSheafUnrestricted l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) X)) :=
    e ≪≫ (DerivedCategory.singleFunctorIsoCompQ _ 0).app _
  exact ⟨(derivedScalarUnit X (coefficientMap l X R E)).symm ≪≫
    (pbcDerivedExtend (coefficientMap l X R E)).mapIso d.symm ≪≫
    ((R.integral E).app K).symm⟩

end WeilConjectures.AdicQbarRealization
