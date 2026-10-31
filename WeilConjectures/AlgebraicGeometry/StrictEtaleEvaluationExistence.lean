/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictEtaleSystemInterfaces
import WeilConjectures.AlgebraicGeometry.CoefficientEvaluationDerivedExtension
import WeilConjectures.AlgebraicGeometry.CoefficientEvaluationDerivedAbove
import WeilConjectures.AlgebraicGeometry.CoefficientEvaluationDerivedBelow
import WeilConjectures.AlgebraicGeometry.CoefficientEvaluationDerivedTransition
import WeilConjectures.AlgebraicGeometry.CoefficientTensorDerivedUnit

/-! # Strict étale evaluation for arbitrary coefficient parameters

Source: Zheng, Construction 4.1, printed p. 21.
The existing component constructions require neither regularity nor completeness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry
attribute [local instance 5000] strictEtaleSystemDerived strictEtaleLevelDerived

/-- The normalized derived evaluation package exists for any coefficient parameter.
Source: Zheng, Construction 4.1, printed p. 21
(blueprint: lem-pur-strict-etale-evaluation-arbitrary-parameter).

Proof: assemble the ordinary evaluation extensions and their normalized adjunctions.
For each quotient map choose the existing universal scalar derived adjunction.
Derive the extensions and exact evaluations using the normalized derived core.
Use the below-level tensor comparison, above-level zero comparison and descended
transitions. Ordinary tensor coherence supplies the unit and associator on complexes.
The universal derived tensor unit agrees with the ordinary unit on representatives:
the complex unit has precisely the ordinary unit as each component. Apply the derived
extension coherence theorem to obtain the representative and composition equations.
Assemble all fields of the package from these components, using the general composite
mate Hom formula for its mate equation. Every component theorem holds for an arbitrary
ring and parameter, so zero rings and zero or unit parameters are covered as well. -/
theorem strictEtaleEvaluation_exists (W : Scheme.{u}) (O : Type (u + 1)) [CommRing O]
    (ell : O) : Nonempty (StrictEtaleEvaluation W O ell) := by
  classical
  let J := W.smallEtaleTopology
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


end AlgebraicGeometry
