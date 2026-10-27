/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedAmbientExchange
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Sheaf.Paper.FiniteProperBaseChange
import all Sheaf.Paper.ProperOpenBoundaryZero
import Sheaf.Paper.IntegralProperBaseChange
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper
import Sheaf.Paper.AdicConstructibilityPredicateComparison
import Sheaf.Paper.BoundedExchangeAmbient
import all Sheaf.Paper.FiniteCoefficientProperFormulaTools
import Sheaf.Paper.CondensedCoefficientIsoExchange

/-!
# Proper base change on the admissible constant-model generators

Source: blueprint sec-six-functors-basics/sk-thm-sfb-proper-base-change and
sk-thm-sf-comp-composition, proper base change in proof (2), with the recorded
coefficient convention of sk-def-localizing-closure.
-/

@[expose] public section

set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

local instance : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _

noncomputable local instance :
    MonoidalCategory (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  Sheaf.monoidalCategory _ _

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor
  condensedAmbientExchange CategoryTheory.mateEquiv CategoryTheory.Functor.mapDerivedCategory

attribute [local instance] finiteProperCache2 finiteProperCache3 finiteProperCache4
  finiteProperCache5 finiteProperCache6 finiteProperCache7 finiteProperCache8
  finiteProperCache9 finiteProperCache10 finiteProperCache12

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  DerivedCategory.monoidalClosed
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard

attribute [local semireducible] residueExchangeUpperStar residueExchangeLowerStar
  residueExchangeAdjunction residueExchangeUpperStarComp

open QuotientChange



attribute [local irreducible] upperStar lowerStar derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarComp moduleObjectDerivedPullback moduleObjectDerivedPushforward

private theorem residue_exchange_eq_condensed
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v) :
    residueExchangeBaseChange R sq.toCommSq = condensedAmbientExchange R sq := by
  have hsquare : residueExchangeSquare R sq.toCommSq =
      condensedAmbientPullbackComparison R sq :=
    transportedCompositeIso_eq (residueExchangeUpperStarComp R q' v).symm
      (residueExchangeUpperStarComp R a q)
      (congrArg (fun h : A ⟶ Y ↦ residueExchangeUpperStar R h) sq.toCommSq.w.symm)
  unfold residueExchangeBaseChange condensedAmbientExchange
  exact congrArg (fun (i : (upperStar R v).leftDerivedFunctor ⋙
      (upperStar R q').leftDerivedFunctor ≅ (upperStar R q).leftDerivedFunctor ⋙
      (upperStar R a).leftDerivedFunctor) ↦
    (mateEquiv (derivedUpperStarLowerStarAdjunction R q)
      (derivedUpperStarLowerStarAdjunction R q') (TwoSquare.mk _ _ _ _ i.hom)).natTrans)
    hsquare

private theorem ambient_iso_of_bounded_iso
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [IsFinitenessCoefficient ℓ R]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [A.Over (Spec (.of k))] [Z.Over (Spec (.of k))]
    [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (A ↘ Spec (.of k))] [QuasiCompact (A ↘ Spec (.of k))]
    [IsSeparated (A ↘ Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    {q : Z ⟶ Y} [q.IsOver (Spec (.of k))]
    {v : Y' ⟶ Y} [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} [a.IsOver (Spec (.of k))]
    {q' : A ⟶ Y'} [q'.IsOver (Spec (.of k))]
    (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory (Modules R Z))
    (hK : boundedConstructible (condensedRingObj R Z) K)
    (hIso : IsIso (boundedConstructibleBaseChange R ℓ
      (sq.toCommSq.asOver (Spec (.of k))))) :
    IsIso ((condensedAmbientExchange R sq).app K) := by
  let C : ProEtale.BoundedConstructible (condensedRingObj R Z) := ⟨K, hK⟩
  have hb := boundedConstructibleBaseChange_hom_eq_ambient R ℓ k sq.toCommSq C
  have hh : IsIso (((boundedConstructibleBaseChange R ℓ
      (sq.toCommSq.asOver (Spec (.of k)))).app C).hom) := by infer_instance
  have he := residue_exchange_eq_condensed R sq
  have hout : IsIso ((condensedAmbientExchange R sq).app C.obj) := by
    apply (congrArg IsIso (hb.trans (congrArg (fun t ↦ t.app C.obj) he))).mp
    refine Eq.mp ?_ hh
    run_tac coefficientCongrGoal
  exact (congrArg (fun J : DerivedCategory (Modules R Z) ↦
    IsIso ((condensedAmbientExchange R sq).app J)) (show C.obj = K from rfl)).mp hout


private theorem rational_adic
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      R = Mon.mk (Profinite.padicAlgClRingObj ℓ)) :
    IsEllAdicCoefficient ℓ R.X inferInstance := by
  rcases hR with ⟨E, hE⟩ | hQ
  · subst R
    exact .continuous E
  · subst R
    exact .algebraicClosure

private theorem rational_finiteness
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      R = Mon.mk (Profinite.padicAlgClRingObj ℓ)) : IsFinitenessCoefficient ℓ R.X := by
  rcases hR with ⟨E, hE⟩ | hQ
  · subst R
    exact .continuous E
  · subst R
    exact .algebraicClosure

private theorem rational_bounded_exchange
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X] [IsFinitenessCoefficient ℓ R.X]
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      R = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y A Y' : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    {q : Z ⟶ Y} [IsProper q.left] {v : Y' ⟶ Y} {a : A ⟶ Z} {q' : A ⟶ Y'}
    (sq : IsPullback a q' q v) :
    IsIso (boundedConstructibleBaseChange R.X ℓ sq.toCommSq) := by
  rcases hR with ⟨E, hE⟩ | hQ
  · subst R
    exact isIso_boundedConstructibleBaseChange_of_isProper ℓ E sq
  · subst R
    exact isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl ℓ sq

private theorem rational_exchange
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X]
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      R = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory (Modules R.X Z))
    (hmodel : constantModelBoundedConstructible R.X Z K) :
    IsIso ((condensedAmbientExchange R.X sq).app K) := by
  have hadic := rational_adic ℓ R hR
  have : IsFinitenessCoefficient ℓ R.X := rational_finiteness ℓ R hR
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace
    (Z ↘ Spec (.of k))
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian
    (Z ↘ Spec (.of k))
  have hK : boundedConstructible (condensedRingObj R.X Z) K := by
    rw [(adicConstructibilityPredicateComparison ℓ Z R.X hadic).2]
    exact hmodel
  have hp : IsPullback a q' q v :=
    IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd
  let : A.Over (Spec (.of k)) := ⟨q' ≫ (Y' ↘ Spec (.of k))⟩
  have : q'.IsOver (Spec (.of k)) := ⟨rfl⟩
  have : a.IsOver (Spec (.of k)) := ⟨by
    change a ≫ (Z ↘ Spec (.of k)) = q' ≫ (Y' ↘ Spec (.of k))
    rw [← comp_over q (Spec (.of k)), ← comp_over v (Spec (.of k))]
    exact sq.toCommSq.w_assoc _⟩
  have : IsProper q' := MorphismProperty.of_isPullback (P := @IsProper) hp inferInstance
  have : LocallyOfFiniteType (A ↘ Spec (.of k)) := by
    change LocallyOfFiniteType (q' ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : QuasiCompact (A ↘ Spec (.of k)) := by
    change QuasiCompact (q' ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have : IsSeparated (A ↘ Spec (.of k)) := by
    change IsSeparated (q' ≫ (Y' ↘ Spec (.of k)))
    infer_instance
  have hs := hp.asOver (Spec (.of k))
  have : IsProper (q.asOver (Spec (.of k))).left := ‹IsProper q›
  have hbc := rational_bounded_exchange ℓ R hR hs
  have hbc' : IsIso (boundedConstructibleBaseChange R.X ℓ
      (sq.toCommSq.asOver (Spec (.of k)))) := by
    refine Eq.mp ?_ hbc
    run_tac coefficientCongrGoal
  exact ambient_iso_of_bounded_iso ℓ R.X k sq K (by
    refine Eq.mp ?_ hK
    run_tac coefficientCongrGoal) (by
    refine Eq.mp ?_ hbc'
    run_tac coefficientCongrGoal)

-- Reuse one elaboration of the finite-Tor predicate for projected monoid objects.
private def GeneratorProperty
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] (Z : Scheme.{u}) :
    ObjectProperty (DerivedCategory (Modules R Z)) :=
  fun K ↦ constantModelBoundedConstructible R Z K ∧ DerivedCategory.finiteTorAmplitude _ K

-- Package the exchange property before classifying coefficient presentations.
private structure GeneratorExchange
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R]
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v) : Prop where
  isIso : ∀ K : DerivedCategory (Modules R Z), GeneratorProperty R Z K →
    IsIso ((condensedAmbientExchange R sq).app K)

attribute [local instance] finiteProperCoefficientMon finiteProperCoefficientComm

attribute [local irreducible] integerIso

private theorem integral_ground_realization (ℓ : ℕ) [Fact ℓ.Prime] :
    ∃ F : PadicAlgCl.FiniteIntermediateField ℓ,
      Nonempty (Mon.mk (Profinite.continuousMapRingObj.{u} ℤ_[ℓ]) ≅
        Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} F.val))) := by
  obtain ⟨F, ⟨eF⟩⟩ := unitBall_realization.{u} ℓ ℚ_[ℓ]
    (PadicInt.subring ℓ) (fun _ ↦ Iff.rfl)
  exact ⟨F, ⟨eF ≪≫ integerIso ℓ F⟩⟩

private theorem admissible_coefficient_induction
    (ℓ : ℕ) [Fact ℓ.Prime]
    (P : (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) →
      [IsCommMonObj R.X] → Prop)
    (hiso : ∀ (R S : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
      [_hR : IsCommMonObj R.X] [_hS : IsCommMonObj S.X],
      (R ≅ S) → P S → P R)
    (hfinite : ∀ (B : Type) [CommRing B] [TopologicalSpace B]
      [DiscreteTopology B] [IsTopologicalRing B] [Finite B],
      (∃ n : ℕ, ∀ b : B, (ℓ ^ n) • b = 0) →
      P (Mon.mk (finiteProperCoefficientRing (ULift.{u} B)).X))
    (hintegral : ∀ F : PadicAlgCl.FiniteIntermediateField ℓ,
      P (Mon.mk (DerivedNakayama.integerRing ℓ (ULift.{u} F.val))))
    (hrational : ∀ F : PadicAlgCl.FiniteIntermediateField ℓ,
      P (Mon.mk (Profinite.continuousMapRingObj F)))
    (hqbar : P (Mon.mk (Profinite.padicAlgClRingObj ℓ)))
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [hΛcomm : IsCommMonObj Λ]
    (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ) : P (Mon.mk Λ) := by
  rcases hΛ with h | h | h | h | h | h
  · obtain ⟨B, _, _, _, _, hfin, ht, ⟨e⟩⟩ := h
    let : Finite B := hfin
    obtain ⟨eB⟩ := finiteBoundaryCoefficientIso.{u} B
    exact hiso _ _ (e ≪≫ eB) (hfinite B ht)
  · obtain ⟨e⟩ := h
    obtain ⟨F, ⟨eF⟩⟩ := integral_ground_realization.{u} ℓ
    exact hiso _ _ (e ≪≫ eF) (hintegral F)
  · obtain ⟨e⟩ := h
    obtain ⟨F, ⟨eF⟩⟩ := field_realization.{u} ℓ ℚ_[ℓ]
    exact hiso _ _ (e ≪≫ eF) (hrational F)
  · obtain ⟨F, ⟨e⟩⟩ := h
    exact hiso _ _ e (hrational F)
  · obtain ⟨F, ⟨e⟩⟩ := h
    exact hiso _ _ (e ≪≫ integerIso ℓ F) (hintegral F)
  · obtain ⟨e⟩ := h
    exact hiso _ _ e hqbar

private theorem exchange_coefficientIso_raw
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S)
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v)
    (h : ∀ J : DerivedCategory (Modules S Z),
      GeneratorProperty S Z J →
      IsIso ((condensedAmbientExchange S sq).app J))
    (K : DerivedCategory (Modules R Z))
    (hK : GeneratorProperty R Z K) :
    IsIso ((condensedAmbientExchange R sq).app K) := by
  let C : ConstantModelConstructibleFiniteTor R Z := by
    refine ⟨K, ?_⟩
    refine Eq.mp ?_ hK
    run_tac coefficientCongrGoal
  have ht := condensedAmbientExchange_coefficientIso e sq (by
    intro J
    exact h J.obj (by
      refine Eq.mp ?_ J.property
      run_tac coefficientCongrGoal)) C
  exact (congrArg (fun J : DerivedCategory (Modules R Z) ↦
    IsIso ((condensedAmbientExchange R sq).app J)) (show C.obj = K from rfl)).mp ht

private theorem finite_exchange_raw
    (ℓ : ℕ) [Fact ℓ.Prime] (B : Type u) [CommRing B] [Finite B]
    (ht : ∃ n : ℕ, (ℓ ^ n) • (1 : B) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory (Modules (finiteProperCoefficientRing B).X Z))
    (hK : GeneratorProperty (finiteProperCoefficientRing B).X Z K) :
    IsIso ((condensedAmbientExchange (finiteProperCoefficientRing B).X sq).app K) := by
  have : IsProper (q.asOver (Spec (.of k))).left := ‹IsProper q›
  have hraw := (finiteProperBaseChange B ℓ ht k
    (Z.asOver (Spec (.of k))) (Y.asOver (Spec (.of k)))
    (q.asOver (Spec (.of k)))).2.1 A Y' v q' a sq ⟨K, by
      refine Eq.mp ?_ hK
      run_tac coefficientCongrGoal⟩
  dsimp only at hraw
  apply (finite_ambient_iso _ sq K).1
  refine Eq.mp ?_ hraw
  run_tac coefficientCongrGoal

private theorem integral_exchange_raw
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory (Modules (DerivedNakayama.integerRing ℓ E) Z))
    (hK : GeneratorProperty (DerivedNakayama.integerRing ℓ E) Z K) :
    IsIso ((condensedAmbientExchange (DerivedNakayama.integerRing ℓ E) sq).app K) := by
  have hraw := (integralProperDirectImageAndFormulas ℓ E k q).2.2.1 v q' a sq
  have hf : ∀ J : DerivedCategory (Modules (DerivedNakayama.integerRing ℓ E) Z),
      constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E) Z J →
      IsIso ((condensedAmbientExchange (DerivedNakayama.integerRing ℓ E) sq).app J) := by
    refine Eq.mp ?_ hraw
    run_tac coefficientCongrGoal
  exact hf K (by
    refine Eq.mp ?_ hK.1
    run_tac coefficientCongrGoal)

private theorem coefficientIso_generator
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (e : Mon.mk R ≅ Mon.mk S)
    {A Z Y Y' : Scheme.{u}} {a : A ⟶ Z} {q' : A ⟶ Y'}
    {q : Z ⟶ Y} {v : Y' ⟶ Y} (sq : ChosenCartesianSquare a q' q v)
    (h : GeneratorExchange S sq) : GeneratorExchange R sq := by
  refine ⟨?_⟩
  intro K hK
  exact exchange_coefficientIso_raw e sq h.isIso K hK

private theorem finite_exchange_generator
    (ℓ : ℕ) [Fact ℓ.Prime] (B : Type u) [CommRing B] [Finite B]
    (ht : ∃ n : ℕ, (ℓ ^ n) • (1 : B) = 0)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    : GeneratorExchange (finiteProperCoefficientRing B).X sq := by
  refine ⟨?_⟩
  intro K hK
  exact finite_exchange_raw ℓ B ht k q v sq K hK

private theorem integral_exchange_generator
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    : GeneratorExchange (DerivedNakayama.integerRing ℓ E) sq := by
  refine ⟨?_⟩
  intro K hK
  have ht := integral_exchange_raw ℓ E k q v sq K (by
    refine Eq.mp ?_ hK
    run_tac coefficientCongrGoal)
  refine Eq.mp ?_ ht
  run_tac coefficientCongrGoal

private theorem rational_generator
    (ℓ : ℕ) [Fact ℓ.Prime]
    (R : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj R.X]
    (hR : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      R = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      R = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    : GeneratorExchange R.X sq := by
  refine ⟨?_⟩
  intro K hK
  have ht := rational_exchange ℓ R hR k q v sq K (by
    refine Eq.mp ?_ hK.1
    run_tac coefficientCongrGoal)
  refine Eq.mp ?_ ht
  run_tac coefficientCongrGoal


/-- The specified proper exchange is invertible on Dctf for every recorded admissible
coefficient, including coefficients isomorphic to the listed representatives.
The square may use any chosen Cartesian realization of the pullback.

Source: blueprint sk-thm-sfb-proper-base-change, finite (2), integral (3), rational (3),
and det-sf-comp-composition-base-change, proof step 2.
(blueprint: lem-sfb-proper-base-change-admissible-generators).

Proof: restrict the scalar extension of a coefficient isomorphism to its exact
inverse-scalar-restriction model. This preserves finite constant models and Tor
amplitude. Choose the normalized scalar/pullback comparisons. Their geometric mates
are invertible because scalar extension is an equivalence. The scalar/geometric
exchange rectangle and cancellation of these comparisons reduce to the coefficient
representative, and scalar extension reflects invertibility.
For finite rings, lift the small scalar ring to the scheme universe, identify its
continuous condensed ring with the sheafified constant ring, and apply finite proper
base change, identifying its pullback-square mate with the specified ambient mate.
For valuation rings apply integral proper base change after the proved coefficient
presentation isomorphism. Realize Z_ell as the unit ball of the degree-one extension.
For finite coefficient fields and the finite-subextension-valued algebraic closure,
compare constant-model and ordinary bounded constructibility on the Noetherian source.
The Cartesian source is proper over Y', so all four schemes satisfy the standing
hypotheses. Apply bounded rational proper base change, then the equality between its
underlying map and the specified ambient mate. Realize Q_ell as a degree-one finite
coefficient extension. These cases exhaust the recorded admissibility predicate;
the full continuous-map algebraic closure is excluded by that predicate. -/
theorem properBaseChange_admissible_generators
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {A Z Y Y' : Scheme.{u}}
    [Z.Over (Spec (.of k))] [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of k))] [QuasiCompact (Z ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    (q : Z ⟶ Y) [q.IsOver (Spec (.of k))] [IsProper q]
    (v : Y' ⟶ Y) [v.IsOver (Spec (.of k))]
    {a : A ⟶ Z} {q' : A ⟶ Y'} (sq : ChosenCartesianSquare a q' q v)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)))
    (hK : constantModelBoundedConstructible Λ Z K ∧ DerivedCategory.finiteTorAmplitude _ K) :
    IsIso ((condensedAmbientExchange Λ sq).app K) := by
  have hP := admissible_coefficient_induction ℓ
    (fun R _ ↦ GeneratorExchange R.X sq)
    (by
      intro R S _ _ e
      have ht := coefficientIso_generator e sq
      refine Eq.mp ?_ ht
      run_tac coefficientCongrGoal)
    (by
      intro B _ _ _ _ _ ht
      obtain ⟨n, hn⟩ := ht
      have ht' : ∃ n : ℕ, (ℓ ^ n) • (1 : ULift.{u} B) = 0 :=
        ⟨n, ULift.ext _ _ (hn 1)⟩
      have hh := finite_exchange_generator ℓ (ULift.{u} B) ht' k q v sq
      refine Eq.mp ?_ hh
      run_tac coefficientCongrGoal)
    (by
      intro F
      have ht := integral_exchange_generator ℓ (ULift.{u} F.val) k q v sq
      refine Eq.mp ?_ ht
      run_tac coefficientCongrGoal)
    (by
      intro F
      have ht := rational_generator ℓ _ (Or.inl ⟨F, rfl⟩) k q v sq
      refine Eq.mp ?_ ht
      run_tac coefficientCongrGoal)
    (by
      have ht := rational_generator ℓ _ (Or.inr rfl) k q v sq
      refine Eq.mp ?_ ht
      run_tac coefficientCongrGoal) Λ hΛ
  have hfinal : ∀ J : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) (condensedRingObj Λ Z)),
      (constantModelBoundedConstructible Λ Z J ∧ DerivedCategory.finiteTorAmplitude _ J) →
      IsIso ((condensedAmbientExchange Λ sq).app J) := by
    refine Eq.mp ?_ hP.isIso
    run_tac coefficientCongrGoal
  exact hfinal K hK

end AlgebraicGeometry.ProEtale.CondensedRing
