/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationModels
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedExtension
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedAbove
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedBelow
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedTransition
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientTensorDerivedUnit

/-!
# Derived extension from a coefficient level

Indices in this module are Zheng's nonnegative indices: `n` denotes the
positive level `n + 1`. No normalization or cartesianness is imposed on a system.
The auxiliary declarations construct the actual strict systems and their evaluations;
the final package records the constructions, universal properties and all coherence laws.

## References

* Stacks Project, Tags 03D7, 06XN, 09T5
* Zheng, Six Operations and Lefschetz--Verdier, Construction 4.1 (printed p. 21)
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w d
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  [HasWeakSheafify J CommRingCat.{w}]
  {O : Type w} [CommRing O] {ell : O} [EssentiallySmall.{w} C]
  [∀ n : ℕ, HasDerivedCategory.{d} (coefficientLevelModules (J := J) O ell n)]
  [HasDerivedCategory.{d} (CoefficientSystem (J := J) O ell)]

-- The original signature retains regularity, although this construction does not need it.
set_option linter.unusedVariables false in
/-- Derived extension from a single varying-coefficient level, with strict models,
coherent truncation maps, and their specified adjunction mates. -/
theorem coefficientEvaluationDerivedLeftAdjoint
    (hregular : ∀ x : O, ell * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({ell} : Set O)) O] :
    Nonempty (CoefficientEvaluationDerivedPackage (J := J) (O := O) (ell := ell)) := by
  classical
  obtain ⟨ordinary⟩ := coefficientOrdinaryEvaluationExtension (J := J) (O := O) (ell := ell)
  let := ordinary.extensionAdditive
  let scalar {m n : ℕ} (h : n ≤ m) :=
    (coefficientScalarDerivedAdjunction (J := J) (O := O) (ell := ell) h).some
  obtain ⟨core⟩ := coefficientEvaluationDerivedCore ordinary
  choose transition ht using (fun (m n : ℕ) (h : n ≤ m) ↦
    coefficientEvaluationDerivedTransition ordinary (fun {_ _} h ↦ scalar h) core h)
  choose below hb using (fun (n q : ℕ) (h : q ≤ n) ↦
    coefficientEvaluationDerivedBelow ordinary (fun {_ _} h ↦ scalar h) core h)
  obtain ⟨strict⟩ := coefficientEvaluationOrdinaryCoherence ordinary
  choose unit hu using (fun n ↦ coefficientTensorDerivedUnit
    (fun {_ _} h ↦ scalar h) n (strict.tensorUnit n))
  have unit_rep (n : ℕ) P : (unit n).hom.app (DerivedCategory.Q.obj P) =
      (scalar (Nat.le_refl n)).counit.app P ≫
        DerivedCategory.Q.map (strict.tensorUnitComplex n P).hom := by
    rw [hu n P]
    congr 1
    apply congrArg
    apply HomologicalComplex.hom_f_injective
    funext i
    change (strict.tensorUnit n).hom.app (P.X i) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (strict.tensorUnitComplex_f n P i).symm
  obtain ⟨derived⟩ := coefficientEvaluationDerivedCoherence ordinary
    (fun {_ _} h ↦ scalar h) core (fun {_ _} h ↦ transition _ _ h) strict unit unit_rep
    (fun h K ↦ ht _ _ h K)
  exact ⟨{
    strictTransition := ordinary.strictTransition
    transitionsNormalized := ordinary.transitionsNormalized
    scalar := fun h ↦ scalar h
    extension := ordinary.extension
    extensionAdditive := ordinary.extensionAdditive
    adj := ordinary.adj
    below := ordinary.below
    above := ordinary.above
    hom_formula := ordinary.hom_formula
    evaluation := core.evaluation
    evaluationFactors := core.evaluationFactors
    derivedExtension := core.derivedExtension
    counit := core.counit
    isDerived := core.isDerived
    computes := fun n P hP _ ↦ core.computes n P hP
    derivedAdj := core.derivedAdj
    transpose := core.transpose
    derivedBelow := fun h ↦ below _ _ h
    derivedAbove := coefficientEvaluationDerivedAbove ordinary core
    transition := fun h ↦ transition _ _ h
    transition_rep := fun h K ↦ ht _ _ h K
    sigma := fun h ↦ coefficientEvaluationSigma (fun {_ _} h ↦ scalar h) core
      (fun {_ _} h ↦ transition _ _ h) h
    mate := fun h ↦ CategoryTheory.Adjunction.compositeMate_homEquiv
      (core.derivedAdj _) (core.derivedAdj _) (scalar h).derivedAdj (transition _ _ h)
    tensorUnit := strict.tensorUnit
    tensorUnit_normalized := strict.tensorUnit_normalized
    tensorAssoc := strict.tensorAssoc
    tensorAssoc_normalized := strict.tensorAssoc_normalized
    strictSigma := strict.strictSigma
    strictSigma_below := strict.strictSigma_below
    strictSigma_above := strict.strictSigma_above
    strictSigmaComplex := strict.strictSigmaComplex
    strictSigmaComplex_f := strict.strictSigmaComplex_f
    sigma_rep := derived.sigma_rep
    tensorUnitComplex := strict.tensorUnitComplex
    tensorUnitComplex_f := strict.tensorUnitComplex_f
    tensorAssocComplex := strict.tensorAssocComplex
    tensorAssocComplex_f := strict.tensorAssocComplex_f
    derivedUnit := unit
    derivedUnit_rep := fun n P _ ↦ unit_rep n P
    derivedAssoc := derived.derivedAssoc
    derivedAssoc_rep := derived.derivedAssoc_rep
    sigma_id := derived.sigma_id
    sigma_comp := derived.sigma_comp
    belowComplex := fun h P ↦
      (NatIso.mapHomologicalComplex (ordinary.below h) (.up ℤ)).app P
    belowComplex_f := fun _ _ _ ↦ rfl
    derivedBelow_rep := fun h P ↦ hb _ _ h P }⟩
end SheafOfModules
