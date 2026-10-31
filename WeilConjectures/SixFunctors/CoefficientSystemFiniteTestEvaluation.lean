/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.SixFunctors.CoefficientSystemFiniteTestPrefix
import WeilConjectures.AlgebraicGeometry.CoefficientNormalizedEvaluationProjection
import WeilConjectures.CategoryTheory.SystemSingleDerivedEvaluation
import WeilConjectures.CategoryTheory.SystemEvaluationTopos
import WeilConjectures.SixFunctors.IntegralDualizingSystemTraceData
import Mathlib.CategoryTheory.Monad.Adjunction

/-! Evaluation of finite representable tests tensored with normalized systems. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
private theorem evaluation_map_bijective_of_iso
    {C : Type*} {D₀ : Type*} [Category* C] [Category* D₀]
    {L : C ⥤ D₀} {E₀ : D₀ ⥤ C} (adj : L ⊣ E₀) [IsIso adj.unit]
    (P : C) {A : D₀} (i : L.obj P ≅ A) (N : D₀) :
    Function.Bijective (fun f : A ⟶ N ↦ E₀.map f) := by
  let eUnit := Iso.homCongr (asIso (adj.unit.app P)) (Iso.refl (E₀.obj N))
  have hLP : Function.Bijective (fun f : L.obj P ⟶ N ↦ E₀.map f) := by
    have he : (fun f : L.obj P ⟶ N ↦ E₀.map f) =
        fun f ↦ eUnit (adj.homEquiv P N f) := by
      funext f
      simp [eUnit, Iso.homCongr, Adjunction.homEquiv_unit]
    rw [he]
    exact eUnit.bijective.comp (adj.homEquiv P N).bijective
  let eA := Iso.homCongr i (Iso.refl N)
  let eB := Iso.homCongr (E₀.mapIso i) (Iso.refl (E₀.obj N))
  have he : (fun f : A ⟶ N ↦ E₀.map f) =
      fun f ↦ eB (E₀.map (eA.symm f)) := by
    funext f
    simp [eA, eB, Iso.homCongr, Functor.map_comp]
  rw [he]
  exact eB.bijective.comp (hLP.comp eA.symm.bijective)

namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

private theorem coefficientEvaluation_adjunction (n : ℕ) :
    ∃ L : normalizedDVRDerived l E X n ⥤ coefficientSequenceDerived l E X,
      ∃ adj : L ⊣ coefficientSequenceDerivedEvaluation l E X n, IsIso adj.unit := by
  classical
  let J := Scheme.ProEt.topology X
  let B := integralCoefficientCommRingSheaf l E X
  let τ := coefficientSequenceCommRingTransition l E X
  let R := SemilinearSections.rings.{u + 1, u, u + 1} J B τ
  let e := SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1} R
  have : e.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive R
  have : e.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive R
  let V := SheafOfModules.derivedSystemEvaluation R n
  let A : SheafOfModules.SystemScalarAssignment.{u + 1, u, u + 1} (J := J) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let H := SheafOfModules.systemTensorCoherence A
  let d := SheafOfModules.systemSingleDerivedExtension R n A H
  have := SemilinearSections.evaluationAdditive.{u + 1, u, u + 1} J B τ n
  have := SemilinearSections.evaluationLimits.{u + 1, u, u + 1} J B τ n
  have := SemilinearSections.evaluationColimits.{u + 1, u, u + 1} J B τ n
  let η : e.inverse ⋙ SheafOfModules.systemEvaluation R n ≅
      SemilinearSections.evaluation.{u + 1, u, u + 1} J B τ n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ =
        (eqToHom (SemilinearSections.evaluation_ring.{u + 1, u, u + 1} J B τ n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β := (Functor.mapDerivedCategoryCompIso e.inverse
      (SheafOfModules.systemEvaluation R n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso η
  let ed := e.mapDerivedCategory
  let L₀ := d.derived ⋙ ed.functor
  let adj₀ : L₀ ⊣ coefficientSequenceDerivedEvaluation l E X n :=
    (d.adjunction.comp ed.toAdjunction).ofNatIsoRight β
  let i : L₀ ⋙ coefficientSequenceDerivedEvaluation l E X n ≅ 𝟭 _ :=
    Functor.isoWhiskerLeft L₀ β.symm ≪≫
      (Functor.associator L₀ ed.inverse V).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator d.derived ed.functor ed.inverse ≪≫
          Functor.isoWhiskerLeft d.derived ed.unitIso.symm ≪≫
          Functor.rightUnitor d.derived) V ≪≫
      SheafOfModules.systemSingleDerivedBelow R (Nat.le_refl n) A H ≪≫ H.derivedUnit R n
  exact ⟨L₀, adj₀, adj₀.isIso_unit_of_iso i⟩

/-- Evaluating a pulled-back representable test tensored with a normalized system
induces a bijection on maps into an arbitrary system. No trace, dualizing object,
finite Tor bound, or constructibility hypothesis is used.

Source: Stacks 07A4, 08J9, 0941; Zheng Construction 4.1 and Proposition 4.17(a).
(blueprint: lem-coef-system-finite-test-evaluation-bijective).

Proof: let L_n be the derived finite-prefix extension, left adjoint to evaluation
at n. Uniqueness of left adjoints, the finite sections comparison, and scalar
extension-restriction identify testPull of the free scalar tower with L_n of the
finite constant scalar test. The normalized evaluation projection identifies its
tensor with M with L_n of the tensor of that finite test with M_n. Below n this is
associativity of scalar extension followed by the normalized transition of M;
above n both objects vanish. The unit of L_n at level n is invertible because the
identity coefficient extension is the identity. Under these identifications the
adjunction Hom equivalence is precisely evaluation of the given map, conjugated
by that unit. It is bijective for arbitrary N. Zero tests, zero systems and n=0
are included, and quotient maps need not be flat. -/
theorem coefficientSystem_finite_test_evaluation_bijective
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (M N : coefficientSequenceDerived l E X)
    (hM : IsNormalizedCoefficientSequence l E X M) (n : ℕ)
    (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E))) :
    Function.Bijective (fun g :
      S.systemClosed.tensor.obj
        ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
          ((coefPairingEvaluationLeft l E n).obj T), M) ⟶ N ↦
      (coefficientSequenceDerivedEvaluation l E X n).map g) := by
  classical
  let Ex := coefficientSequenceDerivedEvaluation l E X n
  obtain ⟨L, adj, hunit⟩ := coefficientEvaluation_adjunction l E X n
  let P := (G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
    ((coefPairingEvaluationLeft l E n).obj T)
  let : IsIso adj.unit := hunit
  let : IsIso (adj.counit.app P) :=
    coefficientSystem_finite_test_prefix D l E X S G n T L adj
  let j := (adj.homEquiv _ _).symm
    ((S.finiteClosed n).tensor.map
      (Prod.mkHom (adj.unit.app (Ex.obj P)) (𝟙 (Ex.obj M))) ≫
        (S.evaluationTensor n).inv.app (L.obj (Ex.obj P), M))
  have hj : IsIso j := coefficientNormalizedEvaluationProjection l E X
    S.toCoefficientDerivedSystemReduction S.evaluationTensor_normalization
      M hM n L adj (Ex.obj P)
  let : IsIso j := hj
  let i := asIso j ≪≫ S.systemClosed.tensor.mapIso
    ((asIso (adj.counit.app P)).prod (Iso.refl M))
  exact evaluation_map_bijective_of_iso adj _ i N

end WeilConjectures
