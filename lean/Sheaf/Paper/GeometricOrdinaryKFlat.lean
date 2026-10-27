/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.GeometricOrdinaryRealization
import all Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.SystemScalarCoherence
import all Sheaf.Paper.SemilinearTensorEvaluation
import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
import all Sheaf.CategoryTheory.SequenceModulePullbackEvaluation

/-! # K-flat preservation for the ordinary geometric realization

Source: Stacks 0G7E; Zheng Construction 4.1.
(blueprint: lem-coef-geometric-ordinary-kflat)
-/
@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option genInjectivity false
set_option genSizeOfSpec false
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (O : GeometryOrdinary.{c, v, r} J B τ J' uInv uPush adjSet)

variable (R : Sheaf J CommRingCat.{max c v r}) (S : Sheaf J' CommRingCat.{max c v r})
  (I : SheafOfModules.AlgebraicInverseImage uInv R S)

include adjSet in
private theorem inverse_kflat [PreservesFiniteLimits uInv] [I.modules.Additive]
    (P : CochainComplex (Mod.{c, v, max c v r} J R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hf : flatTerms.{c, v, r} J R P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := S)
      ((I.modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify J' AddCommGrpCat.{max c v r} := abelianSheafify J'
  let : J'.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J'
  let A : SheafOfModules.SystemScalarModel.{c, v, max c v r} (𝟙 S) :=
    (SheafOfModules.nonempty_systemScalarModel (𝟙 S)).some
  let F := I.modules
  have ht := SheafOfModules.isKFlat_ringedToposPullback uInv uPush adjSet I (𝟙 S)
    (F ⋙ A.model.E) (fun M ↦ A.model.obj_eq (F.obj M))
    (fun f ↦ A.model.map_eq (F.map f)) P hP hf
  let e : F ⋙ A.model.E ≅ F :=
    Functor.isoWhiskerLeft F (SheafOfModules.systemScalarModelUnit rfl A) ≪≫ F.rightUnitor
  exact SheafOfModules.kFlat_iso_independent S
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ht.1

private theorem evaluation_acyclic_iff
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    P.Acyclic ↔ ∀ n : ℕ,
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P).Acyclic := by
  have h : JointlyFaithful (evaluation.{c, v, max c v r} J B τ) := by
    constructor
    intro M N f g h
    ext X x
    exact congrArg (fun k ↦ k.val.app (op X.unop.2) x) (h X.unop.1)
  constructor
  · intro hP n i
    exact (h.jointlyReflectsIsomorphisms.exactAt_iff P i).1 (hP i) n
  · intro hP i
    exact (h.jointlyReflectsIsomorphisms.exactAt_iff P i).2 (fun n ↦ hP n i)

private def evaluation_total_iso (n : ℕ)
    (P Q : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ) :
    (totalTensor.{c, v, r} J (B n)).obj
        ((((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P),
          (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj Q)) ≅
      ((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj
        ((totalTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ)).obj (P, Q)) := by
  let := SheafOfModules.monoidalCategory (systemRing.{c, v, max c v r} J B τ)
  let := SheafOfModules.monoidalCategory (B n)
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (systemRing.{c, v, max c v r} J B τ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients (B n)
  let G := WeilConjectures.SequenceModuleEvaluation.coFor J
    (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
    (evaluation_ring J B τ n)
  let adj := WeilConjectures.SequenceModuleEvaluation.coForAdj J
    (ring (coefficientSequenceTopology J) (systemRing J B τ)) n (ring J (B n))
    (evaluation_ring J B τ n)
  exact (exactTensorTotalIso (evaluation.{c, v, max c v r} J B τ n)
    (ordinaryEvaluationTensor.{c, v, r} J B τ n)
    (evaluation_tensor_natural.{c, v, r} J B τ n)
    G adj).app (P, Q)

private theorem kflat_of_evaluations
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : ∀ n : ℕ, CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J)
      (R := systemRing.{c, v, max c v r} J B τ) P := by
  intro A hA
  apply (evaluation_acyclic_iff.{c, v, r} J B τ _).2
  intro n i
  exact (hP n _ ((evaluation_acyclic_iff.{c, v, r} J B τ A).1 hA n) i).of_iso
    (evaluation_total_iso.{c, v, r} J B τ n A P)

private theorem evaluation_flat (n : ℕ)
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) P)
    (hf : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) P) :
    flatTerms.{c, v, r} J (B n)
      (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P) := by
  let : HasSheafify J AddCommGrpCat.{max c v r} := abelianSheafify J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max c v r} := locallyBijective J
  let : (SheafOfModules.systemSequenceEvaluation (rings J B τ) n).Additive :=
    SheafOfModules.systemSequenceEvaluationAdditive (rings J B τ) n
  let ec := (NatIso.mapHomologicalComplex
    (eqToIso (evaluation_eq_sequence.{c, v, r} J B τ n)) (.up ℤ)).app P
  intro i
  exact SheafOfModules.flatOnSite_of_iso (B n)
    ((HomologicalComplex.eval _ (.up ℤ) i).mapIso ec.symm)
    ((SheafOfModules.systemSequenceEvaluation_preservesKFlat (rings J B τ) n P hP hf).2 i)

include adjSet in
private theorem system_inverse_kflat [PreservesFiniteLimits uInv]
    (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology J) (R := systemRing J B τ) P)
    (hf : flatTerms.{c, v, r} (coefficientSequenceTopology J) (systemRing J B τ) P) :
    CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J')
      (R := systemRing J' O.coefficients O.coefficientTransition)
      ((O.pull.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply kflat_of_evaluations.{c, v, r} J' O.coefficients O.coefficientTransition
  intro n
  have hk := inverse_kflat.{c, v, r} J J' uInv uPush adjSet
    (B n) (O.coefficients n) (O.inverseImage n)
    (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj P)
    (evaluation_kflat.{c, v, r} J B τ n P hP hf)
    (evaluation_flat.{c, v, r} J B τ n P hP hf)
  exact SheafOfModules.kFlat_iso_independent (O.coefficients n)
    ((NatIso.mapHomologicalComplex (O.ordinaryPullEvaluation n) (.up ℤ)).app P).symm hk

/-- The given ordinary inverse image preserves flat-term K-flat representatives at
all coefficient levels and on the sequence site.
Source: Stacks 0G7E; Zheng Construction 4.1.
(blueprint: lem-coef-geometric-ordinary-kflat).

Proof: apply ringed-topos pullback preservation at each level with identity scalar
extension, then remove that extension using the scalar unit. Evaluation preserves
flat-term K-flat complexes. Exact jointly faithful evaluations detect acyclicity;
their right coextension adjoints make tensor evaluation commute with total tensors.
Consequently levelwise K-flatness implies K-flatness of the system. Transport the
levelwise pullbacks through O.ordinaryPullEvaluation to conclude. -/
theorem geometricOrdinary_kflat [PreservesFiniteLimits uInv] :
    (∀ (n : ℕ) (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := B n) P →
      flatTerms.{c, v, r} J (B n) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := J') (R := O.coefficients n)
        (((O.inverseImage n).modules.mapHomologicalComplex (.up ℤ)).obj P)) ∧
    (∀ (P : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J)
        (R := systemRing.{c, v, max c v r} J B τ) P →
      flatTerms.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) P →
      CochainComplex.IsKFlatIndependentCoefficients (J := coefficientSequenceTopology J')
        (R := systemRing.{c, v, max c v r} J' O.coefficients O.coefficientTransition)
        ((O.pull.mapHomologicalComplex (.up ℤ)).obj P)) := by
  constructor
  · intro n P hP hf
    exact inverse_kflat.{c, v, r} J J' uInv uPush adjSet
      (B n) (O.coefficients n) (O.inverseImage n) P hP hf
  · exact system_inverse_kflat.{c, v, r} J B τ J' uInv uPush adjSet O

end WeilConjectures.SemilinearSections
