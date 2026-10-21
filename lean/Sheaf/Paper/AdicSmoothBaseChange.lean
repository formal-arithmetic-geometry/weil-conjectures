/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.IntrinsicCompletionCompleted
public import Sheaf.Paper.CompletedPullback
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicFiniteOperations
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.Paper.IntegralUniformCoefficient
public import Sheaf.Paper.RefinementCoefficientRealization
public import Sheaf.Paper.ProEtaleConstructibleCoefficientSheaf
import Sheaf.Paper.PbcUniformReductionCriterion
import Sheaf.Paper.PbcIntrinsicTowerComplete
import Sheaf.Paper.AdicFiniteExchangeEncoding
import Sheaf.AlgebraicGeometry.FiniteProetaleSmoothBaseChange
import Mathlib.Algebra.CharP.CharAndCard

/-! # Adic smooth base change

Source: blueprint, sec-smooth-base-change/sk-rem-rest, order 1443;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

The exchange is the published completed adjunction mate. The conditional clause
retains all four finite outputs and a single interval for every level.

## Main definitions and statements

- `sbcAdicFiniteCohomology`: the canonical finite coefficient presentation of cohomology.
- `adicSmoothBaseChange`: invertibility and conditional constructible landing.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Cohomology of a finite output, restricted along the canonical constant-to-function
coefficient isomorphism. This changes the coefficient presentation only and introduces
no constructibility or etale-origin condition.
Source: blueprint order 1443, finite-output clause; Stacks 09AJ
(blueprint: sbc-thm-adic-smooth-base-change). -/
def sbcAdicFiniteCohomology (W : Scheme.{u}) (n : ℕ)
    (J : DerivedCategory (pbcModules W ((pbcAdicRings W (pbcIntegralDatum l E)).obj
      (op n)))) (i : ℤ) :
    pbcModules W (adicLisseConstantRing W (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) :=
  (pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom).obj
    ((DerivedCategory.homologyFunctor _ i).obj J)

private theorem sbcConstructible_of_iso
    (W : Scheme.{u}) (A : Type (u + 1)) [CommRing A] [Finite A]
    {M N : pbcModules W (adicLisseConstantRing W A)} (e : M ≅ N)
    (hN : IsConstructibleProEtaleCoefficientModuleSheaf W A N) :
    IsConstructibleProEtaleCoefficientModuleSheaf W A M := by
  obtain ⟨S, hn, hc, hS⟩ := hN
  refine ⟨S, hn, hc, fun i ↦ ?_⟩
  obtain ⟨V, hV, ht⟩ := hS i
  refine ⟨V, hV, fun U f hf ↦ ?_⟩
  obtain ⟨L, hL, ⟨eL⟩⟩ := ht U f hf
  exact ⟨L, hL, ⟨(SheafOfModules.overFunctor _ U).mapIso
    ((proEtaleModuleInverseImage (S.immersion i)
      (adicLisseConstantRing W A)).mapIso e) ≪≫ eL⟩⟩

private theorem sbcMembership_of_finite_comparisons
    (W : Scheme.{u}) [IsNoetherian W] (J : PbcComplete l E W)
    (F : ∀ n : ℕ, DerivedCategory
      (pbcModules W ((pbcAdicRings W (pbcIntegralDatum l E)).obj (op n))))
    (e : ∀ n : ℕ, (sbcReduction l E W n).obj J.obj ≅ F n)
    (a b : ℤ)
    (hF : ∀ (n : ℕ) (i : ℤ),
      IsConstructibleProEtaleCoefficientModuleSheaf W
        (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
        (sbcAdicFiniteCohomology l E W n (F n) i) ∧
      ((i < a ∨ b < i) → IsZero (sbcAdicFiniteCohomology l E W n (F n) i))) :
    PbcIsBoundedConstructibleComplete W (pbcIntegralDatum l E) J.obj := by
  refine ⟨J.property, pbcUniformReductionCriterion_backward l E W J.obj ?_⟩
  refine ⟨a, b, fun n ↦ ?_⟩
  let R := pbcRestrict (pbcLevelConstantComparison W (pbcIntegralDatum l E) n).hom
  let c (i : ℤ) :=
    ((R.mapDerivedCategoryHomologyFunctorIso i).app
      ((sbcReduction l E W n).obj J.obj)).symm ≪≫
    R.mapIso ((DerivedCategory.homologyFunctor _ i).mapIso (e n))
  refine ⟨(DerivedCategory.isGE_iff _ a).2 ?_,
    (DerivedCategory.isLE_iff _ b).2 ?_, ?_⟩
  · intro i hi
    exact ((hF n i).2 (.inl hi)).of_iso (c i)
  · intro i hi
    exact ((hF n i).2 (.inr hi)).of_iso (c i)
  · intro i
    exact sbcConstructible_of_iso W _ (c i) (hF n i).1

set_option backward.isDefEq.respectTransparency false in
private theorem sbcComplete_isIso_of_reductions
    (W : Scheme.{u}) {J L : PbcComplete l E W} (v : J ⟶ L)
    (hv : ∀ n : ℕ, IsIso ((sbcReduction l E W n).map v.hom)) : IsIso v := by
  let d := pbcIntegralDatum l E
  let R := completedReductionTower W d
  have he (n : ℕ) : IsIso
      ((reductionTowerDerivedEvaluation W
        (reductionModuleRing W (d.completedRing W)) n).map (R.map v.hom)) := by
    have := hv n
    exact (NatIso.isIso_map_iff (asIso (completedReductionEvaluation W d n)) v.hom).2
      (inferInstanceAs (IsIso
        ((pbcDerivedRestrict (pbcAdicProjection W d n)).map
          ((sbcReduction l E W n).map v.hom))))
  have : IsIso (R.map v.hom) := by
    rw [DerivedCategory.isIso_iff]
    intro i
    have (n : ℕᵒᵖ) : IsIso
        (((DerivedCategory.homologyFunctor (d.towers W) i).map (R.map v.hom)).app n) := by
      let F := reductionTowerEvaluation W
        (reductionModuleRing W (d.completedRing W)) n.unop
      have he' : IsIso (F.mapDerivedCategory.map (R.map v.hom)) := he n.unop
      have hhom : IsIso ((F.mapDerivedCategory ⋙
          DerivedCategory.homologyFunctor _ i).map (R.map v.hom)) :=
        inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ i).map
          (F.mapDerivedCategory.map (R.map v.hom))))
      exact (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso i)
        (R.map v.hom)).2 inferInstance
    exact NatIso.isIso_of_isIso_app _
  have hJ : IsIso (d.completionUnit W J.obj) :=
    pbcIntrinsicComplete_towerComplete d W J.obj J.property
  have hL : IsIso (d.completionUnit W L.obj) :=
    pbcIntrinsicComplete_towerComplete d W L.obj L.property
  have hn : v.hom ≫ d.completionUnit W L.obj =
      d.completionUnit W J.obj ≫ (completedRlim W (d.completedRing W)).map (R.map v.hom) := by
    dsimp only [AdicCoefficientDatum.completionUnit]
    erw [← Category.assoc, (d.constantRlimAdjunction W).unit.naturality]
    simp only [Functor.comp_map, Category.assoc]
    rw [← Functor.map_comp]
    rw [(completedReductionAugmentation d W).naturality]
    rw [Functor.map_comp]
  have : IsIso (v.hom ≫ d.completionUnit W L.obj) := by
    rw [hn]
    infer_instance
  have : IsIso v.hom := IsIso.of_isIso_comp_right _ (d.completionUnit W L.obj)
  exact (ObjectProperty.isIso_hom_iff _).1 this

/-- Smooth base change for the actual completed adjunction-mate exchange, and
constructible landing under one uniform interval for the four finite systems.
Source: blueprint order 1443, sec-smooth-base-change/sk-rem-rest;
Stacks Tags 0EYU, 099N, 099M and 09AL
(blueprint: sbc-thm-adic-smooth-base-change).

Proof:
1. Use the assumed bounded constructible etale origin of every quotient reduction.
   Exact realization transports it to a fixed-scalar pro-etale object. Finite smooth
   base change applies with annihilator the cardinality of the quotient ring.
   The finite exchange encoding identifies this with the actual finite ringed mate.
2. The published pullback and pushforward reduction comparisons are isomorphisms.
   Their linear natural exchange equation identifies the reduction of the completed
   mate with the finite mate. Cancel the two target comparisons to obtain an
   isomorphism at every quotient level.
3. Exact evaluation commutes with homology. Pointwise invertibility of the strict
   reduction tower map therefore gives its invertibility. The completion-unit
   naturality square and intrinsic completeness of both endpoints then imply
   invertibility of the original completed mate.
4. Under the common-interval hypothesis, transport constructibility and vanishing
   from the specified finite source and target along the same reduction comparisons.
   The backward uniform reduction criterion supplies uniform local models and
   compatible etale origins for both complete endpoints. Fullness and reflection of
   isomorphisms by the full-subcategory inclusion give the final assertion.
-/
theorem adicSmoothBaseChange
    {X S T Y : Scheme.{u}} {f : X ⟶ S} {g : T ⟶ S} {h : Y ⟶ X} {e : Y ⟶ T}
    (sq : ChosenCartesianSquare h e f g)
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [Smooth f] [QuasiCompact g] [QuasiSeparated g]
    (_hT : ∃ d : ℕ, topologicalKrullDim T ≤ (d : WithBot ℕ∞))
    (_hl : IsUnit (l : Γ(S, ⊤)))
    (_horder : ∀ n : ℕ,
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(S, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(X, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(T, ⊤)) ∧
      IsUnit (Nat.card (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) : Γ(Y, ⊤)))
    (K : PbcIntegralConstructible l E T)
    (_horigin : ∀ n : ℕ,
      ∃ L : Etale.BoundedConstructibleDerivedCategory
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n) T,
        Nonempty ((pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n).obj
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1}
              (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)) T).mapDerivedCategory.obj L.obj) ≅
          (sbcReduction l E T n).obj K.obj)) :
    IsIso (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)) ∧
    ((∃ d : ℕ, topologicalKrullDim X ≤ (d : WithBot ℕ∞)) →
      (∃ a b : ℤ, a ≤ b ∧ ∀ n : ℕ, ∀ i : ℤ,
        (IsConstructibleProEtaleCoefficientModuleSheaf S
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E S n
          ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePull l E f n).obj
            ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj))) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf Y
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E Y n
          ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)) i))) ∧
        (IsConstructibleProEtaleCoefficientModuleSheaf X
          (ProEtale.PbcQuotient (pbcIntegralDatum l E) n)
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i) ∧
        ((i < a ∨ b < i) → IsZero
          (sbcAdicFiniteCohomology l E X n
          ((sbcFinitePush l E h n).obj
            ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj))) i)))) →
      ∃ (hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj)
        (hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E)
          ((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj),
        IsIso (ObjectProperty.homMk
          (P := PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E))
          (X := ⟨((sbcPull l E f).obj ((sbcPush l E g).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hB⟩)
          (Y := ⟨((sbcPush l E h).obj ((sbcPull l E e).obj
            ((pbcConstructibleInclusion l E T).obj K))).obj, hD⟩)
          (sbcExchangeApp l E sq ((pbcConstructibleInclusion l E T).obj K)).hom)) := by
  classical
  let Kc := (pbcConstructibleInclusion l E T).obj K
  let B := (sbcPull l E f).obj ((sbcPush l E g).obj Kc)
  let D := (sbcPush l E h).obj ((sbcPull l E e).obj Kc)
  have hfinite (n : ℕ) :
      IsIso (sbcFiniteExchangeApp l E sq n ((sbcReduction l E T n).obj K.obj)) := by
    let A := ProEtale.PbcQuotient (pbcIntegralDatum l E) n
    let R := pbcDerivedFunctionRealization T (pbcIntegralDatum l E) n
    let M := (sbcReduction l E T n).obj K.obj
    let V := R.asEquivalence.inverse.obj M
    obtain ⟨L, ⟨alpha⟩⟩ := _horigin n
    let beta : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj
        L.obj ≅ V := R.asEquivalence.unitIso.app _ ≪≫ R.asEquivalence.inverse.mapIso alpha
    let Q := (ProEtale.finiteCoefficientRealization T A).mapDerivedCategory
    have hW : ProEtale.isBoundedConstructibleFiniteCoefficient T A (Q.obj V) := by
      refine ⟨L.obj, ⟨?_, L.property.2⟩, ⟨?_⟩⟩
      · intro i
        obtain ⟨strata, hs⟩ := L.property.1 i
        exact ⟨strata, strata.isConstructible_stratum, hs⟩
      · exact (Functor.mapDerivedCategoryCompIso
          (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) T)
          (ProEtale.finiteCoefficientRealization T A)).app L.obj ≪≫ Q.mapIso beta
    let : Fintype A := Fintype.ofFinite A
    have hcoeff : Etale.IsSmoothBaseChangeCoefficients (Nat.card A) A S :=
      ⟨Nat.card_pos, inferInstance,
        by simp [Nat.card_eq_fintype_card, Nat.cast_card_eq_zero], (_horder n).1⟩
    have hc := (ProEtale.isIso_finite_proetale_smooth_base_change A sq (Nat.card A)
      hcoeff (Q.obj V) hW).1
    have hi : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
        sq.toCommSq.flip).app (Q.asEquivalence.inverse.obj (Q.obj V))) :=
      isIso_of_reflects_iso _ (ProEtale.finiteCoefficientRealization X A).mapDerivedCategory
    have hdelta : IsIso ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A)
        sq.toCommSq.flip).app V) :=
      (NatTrans.isIso_app_iff_of_iso _ (Q.asEquivalence.unitIso.app V)).2 hi
    obtain ⟨coords⟩ := sbcFiniteExchange_encoding l E sq n M
    apply ((MorphismProperty.isomorphisms _).arrow_iso_iff coords).2
    change IsIso ((pbcDerivedFunctionRealization X (pbcIntegralDatum l E) n).map
      ((ProEtale.derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq.flip).app V))
    infer_instance
  have hred (n : ℕ) :
      IsIso ((sbcReduction l E X n).map (sbcExchangeApp l E sq Kc).hom) := by
    have hfin : IsIso (sbcFiniteExchangeApp l E sq n
        ((sbcReduction l E T n).obj Kc.obj)) := hfinite n
    have hp := (sbcReductionComparisons_isIso l E f n).1 ((sbcPush l E g).obj Kc)
    have hq := (sbcReductionComparisons_isIso l E g n).2 Kc
    have hr := (sbcReductionComparisons_isIso l E h n).2 ((sbcPull l E e).obj Kc)
    have hs := (sbcReductionComparisons_isIso l E e n).1 Kc
    have hc : IsIso ((sbcReduction l E X n).map (sbcExchangeApp l E sq Kc).hom ≫
        sbcPushReduction l E h n ((sbcPull l E e).obj Kc) ≫
          (sbcFinitePush l E h n).map (sbcPullReduction l E e n Kc)) := by
      rw [sbcCompletedOperations_linear_natural_exchange]
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (sbcPushReduction l E h n ((sbcPull l E e).obj Kc) ≫
        (sbcFinitePush l E h n).map (sbcPullReduction l E e n Kc))
  have hiso : IsIso (sbcExchangeApp l E sq Kc) :=
    sbcComplete_isIso_of_reductions l E X _ hred
  refine ⟨hiso, ?_⟩
  intro _hX hinterval
  obtain ⟨a, b, _hab, hinterval⟩ := hinterval
  have hB : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) B.obj := by
    apply sbcMembership_of_finite_comparisons l E X B
      (fun n ↦ (sbcFinitePull l E f n).obj
        ((sbcFinitePush l E g n).obj ((sbcReduction l E T n).obj K.obj)))
      (fun n ↦ ?_) a b (fun n i ↦ (hinterval n i).2.1)
    have := (sbcReductionComparisons_isIso l E f n).1 ((sbcPush l E g).obj Kc)
    have := (sbcReductionComparisons_isIso l E g n).2 Kc
    exact asIso (sbcPullReduction l E f n ((sbcPush l E g).obj Kc)) ≪≫
      (sbcFinitePull l E f n).mapIso (asIso (sbcPushReduction l E g n Kc))
  have hD : PbcIsBoundedConstructibleComplete X (pbcIntegralDatum l E) D.obj := by
    apply sbcMembership_of_finite_comparisons l E X D
      (fun n ↦ (sbcFinitePush l E h n).obj
        ((sbcFinitePull l E e n).obj ((sbcReduction l E T n).obj K.obj)))
      (fun n ↦ ?_) a b (fun n i ↦ (hinterval n i).2.2.2)
    have := (sbcReductionComparisons_isIso l E h n).2 ((sbcPull l E e).obj Kc)
    have := (sbcReductionComparisons_isIso l E e n).1 Kc
    exact asIso (sbcPushReduction l E h n ((sbcPull l E e).obj Kc)) ≪≫
      (sbcFinitePush l E h n).mapIso (asIso (sbcPullReduction l E e n Kc))
  refine ⟨hB, hD, ?_⟩
  have : IsIso (sbcExchangeApp l E sq Kc).hom :=
    (ObjectProperty.isIso_hom_iff _).2 hiso
  exact (ObjectProperty.isIso_hom_iff _).1 this

end WeilConjectures
