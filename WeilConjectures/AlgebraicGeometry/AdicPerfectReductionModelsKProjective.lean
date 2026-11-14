/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicPerfectReductionModelComplexes
import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientTermsProjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! # K-projectivity of ordinary quotient complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] adicResidueLocalReductionStep
  adicResidueConstantPerfect adicResidueRestriction
  adicPerfectLocalComplex derivedExtension extend change
  adicPerfectQuotientComplex adicPerfectQuotientStep

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- K-projectivity of the ordinary quotient complexes (Stacks, Tags 06YY, 064B and 09C5). -/
theorem adicPerfectReductionModels_kprojective (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X)
    (_hU : AdicResidueSliceWeaklyContractible.{u, v} X U)
    (P : CochainComplex (ModuleCat.{max v (u + 1)} A) ℤ)
    (a b : ℤ) (_ha : P.IsStrictlyGE a) (_hb : P.IsStrictlyLE b)
    (_hP : ∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i)) :
    let R := fun n : ℕ ↦
      (finite (coefficientProEtaleModelTopology.{u, v} X) A J n).over U
    let C : (n : ℕ) → Cx (R n) := fun n ↦ adicPerfectQuotientComplex.{u, v} X J U P n
    ∀ n : ℕ, (C n).IsKProjective := by
  dsimp only
  intro n
  let := _hb
  have : ∀ i : ℤ, Projective
      ((adicPerfectQuotientComplex.{u, v} X J U P n).X i) :=
    adicPerfectQuotientComplex_terms_projective.{u, v} X J U _hU P _hP n
  have : (adicPerfectQuotientComplex.{u, v} X J U P n).IsStrictlyLE b := by
    unfold adicPerfectQuotientComplex adicPerfectLocalComplex
    infer_instance
  exact CochainComplex.isKProjective_of_projective _ b

end AlgebraicGeometry.Scheme
