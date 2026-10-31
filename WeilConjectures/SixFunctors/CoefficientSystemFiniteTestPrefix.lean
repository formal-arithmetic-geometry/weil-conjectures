/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.CoefPairingExceptionalTests
import WeilConjectures.CategoryTheory.SystemEvaluationTopos
import WeilConjectures.CategoryTheory.SystemSingleDerivedEvaluation
import Mathlib.CategoryTheory.Monad.Adjunction
import all WeilConjectures.CategoryTheory.CoefficientSequenceGlobalSections
import all WeilConjectures.SixFunctors.CoefHomScalarNaturality
import all WeilConjectures.AlgebraicGeometry.CoefSupportPointSectionsModelExistence

/-! Finite-prefix support of representable scalar tests. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
universe a b c d va vb vc vd

private theorem counit_test_isIso
    {A : Type a} {B : Type b} {C : Type c} {D : Type d}
    [Category.{va} A] [Category.{vb} B] [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ A) (R : A ⥤ C) (a : F ⊣ R)
    (J : D ⥤ C) (V : C ⥤ D) (b : J ⊣ V)
    (L : B ⥤ A) (E : A ⥤ B) (adj : L ⊣ E) [IsIso adj.unit]
    (H : B ⥤ D) (β : R ⋙ V ≅ E ⋙ H) (T : D) :
    IsIso (adj.counit.app (F.obj (J.obj T))) := by
  let ff := adj.fullyFaithfulLOfIsIsoUnit
  let : L.Full := ff.full
  let : L.Faithful := ff.faithful
  let P := F.obj (J.obj T)
  let ε := adj.counit.app P
  let e (N : A) : (P ⟶ N) ≃ (T ⟶ H.obj (E.obj N)) :=
    ((a.homEquiv _ _).trans (b.homEquiv _ _)).trans
      (Iso.homCongr (Iso.refl T) (β.app N))
  have he {N N' : A} (f : P ⟶ N) (g : N ⟶ N') :
      e N' (f ≫ g) = e N f ≫ H.map (E.map g) := by
    dsimp only [e, Equiv.trans_apply]
    rw [a.homEquiv_naturality_right, b.homEquiv_naturality_right]
    simp only [Iso.homCongr_apply, Iso.refl_inv, Category.id_comp]
    change _ ≫ β.hom.app N' = (_ ≫ β.hom.app N) ≫ H.map (E.map g)
    have hn := β.hom.naturality g
    dsimp only [Functor.comp_map] at hn
    simpa only [Category.assoc] using
      congrArg (fun q ↦ (b.homEquiv _ _) ((a.homEquiv _ _) f) ≫ q) hn
  have : IsIso (E.map ε) := inferInstance
  let s : P ⟶ L.obj (E.obj P) :=
    (e _).symm (e P (𝟙 P) ≫ inv (H.map (E.map ε)))
  have hs : s ≫ ε = 𝟙 P := by
    apply (e P).injective
    rw [he]
    dsimp only [s]
    rw [Equiv.apply_symm_apply]
    simp
  refine ⟨⟨s, ?_, hs⟩⟩
  apply (adj.homEquiv _ _).injective
  rw [adj.homEquiv_unit]
  change adj.unit.app _ ≫ E.map (ε ≫ s) = adj.unit.app _ ≫ E.map (𝟙 _)
  apply (cancel_epi (adj.unit.app _)).mpr
  apply (cancel_mono (E.map ε)).mp
  rw [← E.map_comp, ← E.map_comp]
  simp only [Category.assoc, hs, Category.id_comp]
  exact congrArg E.map (Category.comp_id ε)

private theorem evaluation_unit_isIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u}) (n : ℕ)
    (L : normalizedDVRDerived l E W n ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceDerivedEvaluation l E W n) : IsIso adj.unit := by
  classical
  have : (coefficientSequenceEvaluation l E W n).Additive :=
    coefficientSequenceEvaluation_additive l E W n
  have : PreservesFiniteLimits (coefficientSequenceEvaluation l E W n) :=
    (coefficientSequenceEvaluation_exact l E W n).1
  have : PreservesFiniteColimits (coefficientSequenceEvaluation l E W n) :=
    (coefficientSequenceEvaluation_exact l E W n).2
  let B := coefficientSequenceCommRingSystem.{u, u} l E W
  let e := SheafOfModules.strictSystemSequenceEquivalence B
  have : e.functor.Additive := SheafOfModules.strictSystemToSequenceAdditive B
  have : e.inverse.Additive := SheafOfModules.sequenceToStrictSystemAdditive B
  let S : SheafOfModules.SystemScalarAssignment.{u + 1, u, u + 1}
      (J := ProEt.topology W) :=
    fun φ ↦ Classical.choice (SheafOfModules.nonempty_systemScalarModel φ)
  let T := SheafOfModules.systemTensorCoherence S
  let d := SheafOfModules.systemSingleDerivedExtension B n S T
  let h : e.inverse ⋙ SheafOfModules.systemEvaluation B n ≅
      coefficientSequenceEvaluation l E W n :=
    SheafOfModules.pushforwardCongr (by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext U
      change 𝟙 _ = (eqToHom (coefficientSequenceEvaluationRing_eq l E W n).symm).hom.app U
      rw [ObjectProperty.eqToHom_hom, eqToHom_app]
      rfl)
  let β : e.mapDerivedCategory.inverse ⋙ SheafOfModules.derivedSystemEvaluation B n ≅
      coefficientSequenceDerivedEvaluation l E W n :=
    (Functor.mapDerivedCategoryCompIso e.inverse
      (SheafOfModules.systemEvaluation B n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso h
  let a := (d.adjunction.comp e.mapDerivedCategory.toAdjunction).ofNatIsoRight β
  let γ := adj.leftAdjointUniq a
  let μ : d.derived ⋙ SheafOfModules.derivedSystemEvaluation B n ≅ 𝟭 _ :=
    SheafOfModules.systemSingleDerivedBelow B (Nat.le_refl n) S T ≪≫ T.derivedUnit B n
  let i : L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅ 𝟭 _ :=
    Functor.isoWhiskerRight γ _ ≪≫
      Functor.isoWhiskerLeft (d.derived ⋙ e.mapDerivedCategory.functor) β.symm ≪≫
      Functor.isoWhiskerRight
        (Functor.isoWhiskerLeft d.derived e.mapDerivedCategory.unitIso.symm) _ ≪≫ μ
  exact adj.isIso_unit_of_iso i

private theorem test_sections_evaluation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (W : Scheme.{u}) (n : ℕ) :
    Nonempty (coefPairingSections l E W ⋙ coefPairingDerivedEvaluation l E n ≅
      coefficientSequenceDerivedEvaluation l E W n ⋙
        coefficientFiniteDerivedRestriction l E W n ⋙
          CoefSupportOpenTensor.levelSections l E W) := by
  let f := (Functor.whiskeringRight ℕᵒᵖ _ _).obj (coefTraceConstantScalars l E W)
  let g := coefTraceSections l E W
  let r := coefficientSequenceRestriction l E W
  let c : coefPairingSections l E W ≅
      coefficientSequenceDerivedRestriction l E W ⋙
        CoefSupportOpenTensor.integralSections l E W :=
    Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso r f) g.rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft r.mapDerivedCategory
        (derivedComposite f g (fun I hI ↦ by
          have := hI
          exact coefCompletedTowerSections_acyclic l E W I)).symm
  let F := CoefSupportOpenTensor.ordinaryLevelSections l E W
  let P := CoefSupportOpenTensor.actualSectionsDerivedPair F
  let T := CoefSupportOpenTensor.actualSectionsDerivedPair
    (CoefSupportOpenTensor.ordinarySections l E W)
  obtain ⟨β, _, _⟩ := SheafOfModules.coefficientTowerComparison F P T (fun K ↦ by
    obtain ⟨I, hI, a, _, ha⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective K
    exact ⟨I, a, hI, ha⟩)
  exact ⟨Functor.isoWhiskerRight c (coefPairingDerivedEvaluation l E n) ≪≫
    Functor.isoWhiskerLeft (coefficientSequenceDerivedRestriction l E W) (β (op n)) ≪≫
    Functor.isoWhiskerRight (coefficientRestrictedEvaluationIso l E W n)
      (CoefSupportOpenTensor.levelSections l E W)⟩

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/-- Finite evaluation is a localization on a pulled-back representable scalar
test: the counit at this test is invertible.
This concerns only the test, before tensoring with a normalized input.

Source: Stacks 07A4, 0941; Zheng Construction 4.1.
(blueprint: lem-coef-system-finite-test-prefix).

Proof: construct the finite-prefix left extension. At a level m at most n its
value is derived coefficient extension from the nth ring to the mth ring, and
above n it is zero. Evaluation at n is the identity coefficient extension, so
the derived unit is invertible. The source sections adjunction of G, composed
with the free-tower/evaluation adjunction, is a left adjoint of source sections
followed by nth scalar evaluation. The normalized sections evaluation comparison
identifies this right adjoint with finite evaluation followed by finite scalar
sections. Uniqueness of left adjoints compares its left adjoint with finite-prefix
extension of the finite constant scalar test. The comparison identifies the counit
at the supplied pulled-back test with the identity-level coefficient counit and
the adjunction triangle; hence it is invertible. Transport to the arbitrary
supplied L and adj by the unique unit-compatible isomorphism of left adjoints.
This proof uses neither normalized tensor inputs nor finite duality; the zero test
and n=0 satisfy the same identity-level calculation. -/
theorem coefficientSystem_finite_test_prefix
    (S : CoefficientDerivedSystemCalculus l E X)
    (G : CoefPairingSystem l E (finiteDualizingCompactification D X) S)
    (n : ℕ) (T : DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)))
    (L : normalizedDVRDerived l E X n ⥤ coefficientSequenceDerived l E X)
    (adj : L ⊣ coefficientSequenceDerivedEvaluation l E X n) :
    IsIso (adj.counit.app
      ((G.frame.testPull S.systemClosed G.baseTensors.systemClosed).obj
        ((coefPairingEvaluationLeft l E n).obj T))) := by
  have : IsIso adj.unit := evaluation_unit_isIso l E X n L adj
  obtain ⟨β⟩ := test_sections_evaluation l E X n
  exact counit_test_isIso
    (G.frame.testPull S.systemClosed G.baseTensors.systemClosed)
    (coefPairingSections l E X) G.frame.sourceAdjunction
    (coefPairingEvaluationLeft l E n) (coefPairingDerivedEvaluation l E n)
    (coefPairingEvaluationAdjunction l E n) L
    (coefficientSequenceDerivedEvaluation l E X n) adj _ β T

end WeilConjectures
