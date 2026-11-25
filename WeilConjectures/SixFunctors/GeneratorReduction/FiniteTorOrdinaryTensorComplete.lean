/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralSystemRealization.Canonical.IntegralSystemCanonicalBridge
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.SixFunctors.GeneratorReduction.FiniteTorAffineProjectiveCharts
import WeilConjectures.SixFunctors.GeneratorReduction.AffineTreeCompleteDetection
import WeilConjectures.SixFunctors.GeneratorReduction.ProjectiveChartOrdinaryTensorModel
import WeilConjectures.SixFunctors.GeneratorReduction.BoundedProjectiveComplexCompleteUnrestricted
import WeilConjectures.SixFunctors.IntegralOnSlice.QcqsCompletionUnitCriterion

/-! # Completeness of the ordinary tensor of finite-Tor integral inputs

The ordinary ambient tensor of two complete bounded constructible integral complexes with
uniform finite Tor amplitude is derived complete.

## Main results

- `finiteTorOrdinaryTensorComplete`

## Implementation details

Completeness is detected on affine opens, refined along the constructible stratifications of
both residue complexes and weakly contractible pro-etale affine covers. There derived
completeness and the uniform finite Tor bounds lift the bounded finite-projective residue
models to bounded finite-projective models over the completed coefficient sheaf. Their
ordinary total tensor is again a bounded complex of finite-projective modules, hence complete,
and the K-flat representative comparison identifies it with the ambient tensor. The argument
concerns only completeness and introduces no choice of comparison map.

## References

- B. Bhatt, P. Scholze, *The pro-étale topology for schemes*, Lemma 6.5.5.
- Stacks Project, Tag 099N.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory AlgebraicGeometry
attribute [local irreducible] HasDerivedCategory.standard
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  WeilConjectures.pullbackTensorCalculus
namespace WeilConjectures.GeneratorReduction
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The ordinary ambient tensor of two complete bounded constructible integral complexes
with uniform finite Tor amplitude is derived complete. -/
theorem finiteTorOrdinaryTensorComplete (X : Scheme.{u})
    (K L : DerivedCategory (scalarReductionSource l E X))
    (hK : finiteTorConstructibleIntegral l E X K)
    (hL : finiteTorConstructibleIntegral l E X L) :
    IntegralOnSlice.IsComplete l E X none
      ((IntegralSystemRealization.calculus l E X).integralClosed.tensor.obj (K, L)) := by
  apply affineTreeCompleteDetection.{u, u} l E X
  intro U hU
  let := hU
  obtain ⟨tree, htree⟩ := finiteTorAffineProjectiveCharts l E X K L hK hL U
  refine ⟨tree, ?_⟩
  intro S p hp hS
  obtain ⟨c, A, hqc, hqs, hcover, hmodels⟩ := htree S p hp hS
  refine ⟨c, A, hqc, hqs, hcover, ?_⟩
  intro i
  let : CompactSpace (A i).left := hqc i
  let : QuasiSeparatedSpace (A i).left := hqs i
  obtain ⟨P, hbP, hP, eP⟩ := hmodels i K (.inl rfl)
  obtain ⟨Q, hbQ, hQ, eQ⟩ := hmodels i L (.inr rfl)
  obtain ⟨V, hbV, hV, ⟨eV⟩⟩ := projectiveChartOrdinaryTensorModel l E
    (X := X) (T := (A i).left)
    ((A i).hom ≫ p.toRoot ≫ U.ι) K L P Q hbP hbQ hP hQ eP eQ
  have hc := boundedProjectiveComplex_complete.{u, u} l E (A i).left V hbV hV
  have hu := (IntegralOnSlice.canonicalCompletionUnitCriterion.{u, u} l E (A i).left _).mpr hc
  let η := IntegralOnSlice.completionUnit.{u, u} l E (A i).left none
  let F := IntegralOnSlice.completion.{u, u} l E (A i).left none
  apply (IntegralOnSlice.canonicalCompletionUnitCriterion.{u, u} l E (A i).left _).mp
  have : IsIso (η.app (DerivedCategory.Q.obj V)) := hu
  have hn := η.naturality eV.hom
  have : IsIso (η.app _ ≫ F.map eV.hom) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map eV.hom)

end WeilConjectures.GeneratorReduction
