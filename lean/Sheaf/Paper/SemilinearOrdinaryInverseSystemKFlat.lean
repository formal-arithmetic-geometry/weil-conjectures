/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.SemilinearOrdinaryInverseSystem
import Sheaf.CategoryTheory.SystemEvaluationKFlat
import Sheaf.CategoryTheory.SystemScalarCoherence
import all Sheaf.Paper.KFlatRingedToposPullback
import all Sheaf.Paper.SemilinearTotalTensorEvaluation
import all Sheaf.Paper.SemilinearSystemsExistence

/-! # K-flatness for ordinary inverse systems

Source: Zheng Construction 4.1; Stacks, lemma-pullback-K-flat.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe c v r
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r}) (τ : ∀ n, B (n + 1) ⟶ B n)
  {D : Type c} [Category.{v} D] [EssentiallySmall.{max c v r} D]
  (J' : GrothendieckTopology D)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adj : uInv ⊣ uPush) [PreservesFiniteLimits uInv]
  (F : ℕ → Sheaf J' CommRingCat.{max c v r}) (σ : ∀ n, F (n + 1) ⟶ F n)
  (I : ∀ n, SheafOfModules.AlgebraicInverseImage uInv (B n) (F n))

private theorem evaluation_sequence (n : ℕ) :
    evaluation.{c, v, max c v r} J B τ n =
      SheafOfModules.systemSequenceEvaluation (rings.{c, v, max c v r} J B τ) n := by
  unfold evaluation SheafOfModules.systemSequenceEvaluation
  congr 1
  ext U x
  rw [ObjectProperty.eqToHom_hom, eqToHom_app]
  rfl

include uPush adj in
private theorem finite_kflat (n : ℕ) [(I n).modules.Additive]
    (P : CochainComplex (Mod.{c, v, max c v r} J (B n)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (R := B n) P)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := B n) (P.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := F n)
      (((I n).modules.mapHomologicalComplex (.up ℤ)).obj P) := by
  let A : SheafOfModules.SystemScalarModel (J := J') (𝟙 (F n)) :=
    (SheafOfModules.nonempty_systemScalarModel (J := J') (𝟙 (F n))).some
  let T := (I n).modules ⋙ A.model.E
  have ht := SheafOfModules.isKFlat_ringedToposPullback uInv uPush adj (I n) (𝟙 (F n)) T
    (fun M ↦ A.model.obj_eq ((I n).modules.obj M))
    (fun f ↦ A.model.map_eq ((I n).modules.map f)) P hP hf
  let e : T ≅ (I n).modules := Functor.isoWhiskerLeft (I n).modules
    (SheafOfModules.systemScalarModelUnit rfl A) ≪≫ (I n).modules.rightUnitor
  exact SheafOfModules.kFlat_iso_independent (F n)
    ((NatIso.mapHomologicalComplex e (.up ℤ)).app P) ht.1

include uPush adj in
/-- An ordinary inverse system carries flat-term K-flat complexes to K-flat complexes.
Source: Zheng Construction 4.1; Stacks sites-cohomology, lemma-pullback-K-flat.
(blueprint: lem-coef-ordinary-inverse-system-kflat).

Proof: evaluate the source complex at each level. Vertical evaluation is a ringed-topos
inverse image, so preserves both flatness and K-flatness for complexes with flat terms.
Apply the same pullback theorem to the algebraic inverse image I at that level.
The component isomorphism of P identifies this with evaluation of the whole inverse
image. To detect K-flatness of that image, tensor with any acyclic system complex.
Evaluation is exact and commutes with total tensor, so each evaluated tensor is acyclic.
Exactness on the vertical sequence site is detected at every level, giving acyclicity
of the original tensor and hence K-flatness. -/
theorem ordinaryInverseSystem_kflat [∀ n, (I n).modules.Additive]
    (P : OrdinaryInverseSystem.{c, v, r} J B τ J' uInv F σ I) [P.pull.Additive]
    (K : CochainComplex (Systems.{c, v, max c v r} J B τ) ℤ)
    (hK : CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J B τ) K)
    (hf : ∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := coefficientSequenceTopology J)
      (R := systemRing.{c, v, max c v r} J B τ) (K.X i)) :
    CochainComplex.IsKFlatIndependentCoefficients (R := systemRing.{c, v, max c v r} J' F σ)
      ((P.pull.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hk (n : ℕ) := SheafOfModules.systemSequenceEvaluation_preservesKFlat
    (rings.{c, v, max c v r} J B τ) n K hK hf
  have he (n : ℕ) := finite_kflat.{c, v, r} J B J' uInv uPush adj F I n
    (((evaluation.{c, v, max c v r} J B τ n).mapHomologicalComplex (.up ℤ)).obj K)
    (by simpa only [← evaluation_sequence.{c, v, r}] using (hk n).1)
    (by simpa only [← evaluation_sequence.{c, v, r}] using (hk n).2)
  have hout (n : ℕ) : CochainComplex.IsKFlatIndependentCoefficients (R := F n)
      (((evaluation.{c, v, max c v r} J' F σ n).mapHomologicalComplex (.up ℤ)).obj
        ((P.pull.mapHomologicalComplex (.up ℤ)).obj K)) := by
    let e := (NatIso.mapHomologicalComplex (P.component n) (.up ℤ)).app K
    exact SheafOfModules.kFlat_iso_independent (F n) e.symm (he n)
  let T := (P.pull.mapHomologicalComplex (.up ℤ)).obj K
  let R := systemRing.{c, v, max c v r} J' F σ
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  intro Z hZ i
  apply (systemsComponentwise.{c, v, r} J' F σ _).2
  intro n
  have hn : (((evaluation.{c, v, max c v r} J' F σ n).mapHomologicalComplex
      (.up ℤ)).obj Z).Acyclic := by
    intro j
    exact (hZ j).map (evaluation.{c, v, max c v r} J' F σ n)
  exact (hout n _ hn i).of_iso (WeilConjectures.evaluationTotalIso.{c, v, r} J' F σ n Z T).symm

end WeilConjectures.SemilinearSections
