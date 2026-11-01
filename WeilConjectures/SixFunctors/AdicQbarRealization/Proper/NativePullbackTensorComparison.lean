/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativeProperTensorComparison
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCoefficientMap
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackCochainTensor
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackDerivedTensor
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackExactCounits
import WeilConjectures.SixFunctors.AdicQbarRealization.Proper.NativePullbackUnit

/-! # Normalized ambient tensor and unit data for native pullback

Source: Stacks Tags 03EL and 07A4; Bhatt--Scholze Remark 6.8.15.
(blueprint: lem-sf-native-pullback-tensor-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization.Proper

/-- The chosen ordinary and derived native pullback has normalized tensor and unit
comparisons for the specified ambient closed structures. Source: Stacks 03EL, 07A4.
(blueprint: lem-sf-native-pullback-tensor-comparison).

Proof: transfer the ordinary ringed total tensor comparison by adjunction uniqueness;
its canonical unit equation gives pure normalization. Pullback preserves every K-flat
complex by the stalk criterion and scalar cancellation. Descend the cochain comparison
through K-flat localization to obtain the representative-normalized derived tensor
comparison. Pullback of the regular module, placed in degree zero, gives the ordinary
unit isomorphism. Compose the specified source unit model, the normalized pull counit,
localization of the ordinary unit isomorphism, and the inverse target unit model to
obtain the derived unit. Cancellation of the target unit model proves its representative
equation. These constructions fill every field of TensorComparison. -/
theorem nativePullbackTensorComparison (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (R : LocallyFiniteAdicRealization.Realization l X)
    (S : LocallyFiniteAdicRealization.Realization l Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (O : Operations l p R S) (A : At l X R) (C : At l Y S) :
    Nonempty (TensorComparison l p R S O A C) := by
  have := nativePullbackCoefficient_isIso l p R S O
  obtain ⟨cochain, hpure⟩ := nativePullbackCochainTensor l p R S O A C
  obtain ⟨tensor, htensor, _⟩ := nativePullbackDerivedTensor l p R S O A C cochain
  obtain ⟨unitCochain, hunit⟩ := nativePullbackUnit l p R S O A C
  let LF := ContinuousRational.derivedPull p O.coefficient
  have : IsIso (O.pullCounit.app
      (ringedTensorUnitComplex.{u + 1, u, u + 1} (ProEt.topology Y) (ring l Y S))) :=
    nativePullbackNormalizedCounit_isIso p O.coefficient O.pullCounit O.pull_normalized _
  let unit := LF.mapIso C.coherence.unitIso ≪≫ asIso (O.pullCounit.app _) ≪≫
    DerivedCategory.Q.mapIso unitCochain ≪≫ A.coherence.unitIso.symm
  refine ⟨{
    cochain := cochain
    pure := hpure
    kflat := fun P hP ↦ nativePullbackKFlat p O.coefficient P hP
    tensor := tensor
    representative := htensor
    unitCochain := unitCochain
    unit_sections := hunit
    unit := unit
    unit_representative := ?_ }⟩
  change LF.map C.coherence.unitIso.hom ≫ O.pullCounit.app _ ≫
    DerivedCategory.Q.map unitCochain.hom = unit.hom ≫ A.coherence.unitIso.hom
  dsimp only [unit, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end WeilConjectures.AdicQbarRealization.Proper
