/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteModelQuotient.FiniteModelSheafQuotientConstructible
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientModelComparison
import all WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Positive integral reduction on qcqs schemes -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

private theorem qcqs_finite_sheaf_criterion
    (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [Finite A] [DiscreteTopology A]
    (enc : ∀ X : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A X)
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (N : FiniteDiscreteOrdinary.Internal A X) :
    IsConstantModelConstructible (FiniteDiscreteOrdinary.coefficient A) X N ↔
      Scheme.IsConstructibleProEtaleModuleSheaf X A ((enc X).ordinary.functor.obj N) := by
  have hqc : CompactSpace X ∧ QuasiSeparatedSpace X := ⟨inferInstance, inferInstance⟩
  rw [IsConstantModelConstructible, if_pos hqc]
  constructor
  · rintro ⟨S, hS⟩
    have h := (FiniteDiscreteOrdinary.strataComparison A enc X N S).mp hS
    let F := ((enc X).ordinary.functor ⋙ (enc X).fixed.functor).obj N
    have hc : IsConstructible (ULift.{u + 1} A) F := by
      refine ⟨S, fun i ↦ ?_⟩
      have hi := (Scheme.finiteLocal_iff (S.domain i) A _).mpr (h i)
      let e := (Scheme.proEtaleModuleRestriction_pullback (S.immersion i) A
        ((enc X).ordinary.functor.obj N)).some ≪≫
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (S.immersion i)).mapIso
          (FiniteDiscreteOrdinary.fixedIso A X (enc X)
            ((enc X).ordinary.functor.obj N)).symm
      exact isFiniteLocallyConstant_of_iso e hi
    exact (Scheme.proEtaleModuleRestriction_constructible_iff X A _).mpr
      (isConstructible_of_iso (FiniteDiscreteOrdinary.fixedIso A X (enc X) _) hc)
  · rintro ⟨S, hn, hS⟩
    exact ⟨S, (FiniteDiscreteOrdinary.strataComparison A enc X N S).mpr hS⟩

/-- Every positive uniformizer reduction of a bounded finite constant-model
constructible integral complex on a qcqs scheme is bounded constructible.

Source: blueprint latest, lem-integral-ctf-equals-bc, Local models and Complexes;
Stacks Tags 093M, 06YY and 06UQ
(blueprint: lem-sfb-integral-qcqs-positive-reduction-constructible).

Proof: the normalized finite coefficient encoding identifies finite constant local
models with locally constant finite-stalk models on each stratum. On a qcqs scheme
the input's definition is a single global finite stratification, so this comparison
requires no Noetherian hypothesis. The finite-model sheaf quotient theorem computes
reduction of each constructible sheaf in degree zero by a two-term finite free
matrix and proves bounded constructibility. Intrinsic finite-coefficient bounded
constructibility is triangulated. Pull it back along derived reduction followed
by the exact normalized encoding; derived reduction is triangulated because it is
left adjoint to exact restriction. Finite truncation devissage now proves the
property for every bounded complex whose homology sheaves are constructible.
Finally transfer back through the finite coefficient criterion. The argument
allows the zero complex, empty scheme, zero ranks and the first positive quotient. -/
theorem integralReduction_qcqs_constantModelBoundedConstructible
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing l E) X K)
    (n : ℕ) :
    constantModelBoundedConstructible (DerivedNakayama.quotientRing l E (n + 1)) X
      ((AdicCompletion.derivedReduction l E X n).obj K) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1) (by omega)
  let : DiscreteTopology A := FiniteModelQuotient.finiteTopology_discrete l E n
  let enc : ∀ Y : Scheme.{u}, FiniteDiscreteOrdinary.Encoding A Y :=
    fun Y ↦ (FiniteDiscreteOrdinary.encoding_exists A Y).some
  let e := enc X
  have hc := qcqs_finite_sheaf_criterion A enc X
  have criterion := FiniteDiscreteOrdinary.derived_boundedConstructible A X e hc
  let B := FiniteDiscreteOrdinary.ordinaryIntrinsicBoundedConstructible A X
  have hB : B = (fun L : Scheme.proEtaleDerivedCategory X A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor _ i).obj L)} ∧
      ∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf X A
        ((DerivedCategory.homologyFunctor _ i).obj L)) := by
    funext L
    apply propext
    change (_ ∧ _) ↔ (_ ∧ _)
    rw [Scheme.finite_homology_support_iff_bounded]
  have : B.IsClosedUnderIsomorphisms := by
    rw [hB]
    exact (Scheme.proEtale_bounded_constructible_isTriangulated X A).1
  have : B.IsTriangulated := by
    rw [hB]
    exact (Scheme.proEtale_bounded_constructible_isTriangulated X A).2
  let adj := Mod.derivedExtendMapDerivedCategoryAdjunction (AdicCompletion.quotient l E X n)
  let := adj.leftAdjointCommShift ℤ
  have := adj.commShift_of_rightAdjoint ℤ
  have : (AdicCompletion.derivedReduction l E X n).IsTriangulated :=
    adj.isTriangulated_leftAdjoint
  let : e.ordinaryDerived.functor.CommShift ℤ := by
    change e.ordinary.functor.mapDerivedCategory.CommShift ℤ
    infer_instance
  have : e.ordinaryDerived.functor.IsTriangulated := by
    change e.ordinary.functor.mapDerivedCategory.IsTriangulated
    infer_instance
  let F := AdicCompletion.derivedReduction l E X n ⋙ e.ordinaryDerived.functor
  let Q := B.inverseImage F
  let P := ObjectProperty.isoClosure
    (IsConstantModelConstructible (DerivedNakayama.integerRing l E) X)
  have hsingle (N : AdicCompletion.Modules l E X) (hN : P N) :
      Q ((DerivedCategory.singleFunctor _ 0).obj N) := by
    obtain ⟨N', hN', ⟨j⟩⟩ := hN
    have h := (FiniteModelQuotient.finite_model_sheaf_quotient_constructible
      l E X N' hN' n).choose_spec.2.2.1
    exact Q.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso j).symm
      ((criterion _).mp h)
  have hQ : Q K := DerivedCategory.prop_of_bounded Q P hsingle K hK.1
    (fun q ↦ ⟨_, hK.2 q, ⟨Iso.refl _⟩⟩)
  exact (criterion _).mpr hQ

end AlgebraicGeometry.ProEtale
