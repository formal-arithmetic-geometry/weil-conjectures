/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S6
-/
module

public import Sheaf.Paper.PurSequenceAdjointResolutionData
import Sheaf.Paper.SequenceKInjectiveComparisonShifts
import Sheaf.Paper.PurSequenceComparisonTranspose

/-! # Derived normalization for a factored quotient projection

Source: Stacks Project, Tags 06YY, 09T5 and 0D6E
(blueprint: lem-pur-sequence-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The factored quotient projection has universal derived adjoints with the
specified simultaneous-resolution normalization and coefficient comparisons.
Source: Stacks 06YY, 09T5, 070I and 0D6E; blueprint coefficient-comparison paragraph
of `fix-prop-coherence.proof.md`
(blueprint: lem-pur-sequence-derived-normalization).

Proof: derive the ordinary pullback on flat-term K-flat resolutions. Its strict
quotient tensor complex is the common resolving model of the supplied reduction;
uniqueness of normalized descent gives the comparison with that reduction and
the left-model equation. Derive the ordinary direct image on K-injective systems.
In the given constant-ring factorization, the first direct image is exact scalar
restriction. The derived-composition theorem therefore compares the universal
right-derived functor with total inverse limit. For a K-injective system I and
any K-injective replacement j of its restricted tower, this comparison is the
class of lim(j), and lim(j) is a quasi-isomorphism. This proves the right-model
and composition-model fields, with the prescribed canonical replacement iso.
The resolving-class derived-adjunction theorem gives the chain-map transpose
formula for every complex Q, target I and map f. On resolving representatives
these are the ordinary tensor/limit transposes. K-flat and K-injective resolutions
cover the full derived Hom sets, so the canonical comparisons identify the
specified coefficient adjunction on all inputs. Identity transposes give its unit
and counit equations. Naturality of the universal comparisons makes all of these
equations independent of choices of representatives. The restricted tower of I
is not assumed K-injective, and evaluation is not used as a faithfulness test. -/
theorem purSequenceDerivedNormalization
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (H : PurSequenceRingedFactorization l E W O) :
    Nonempty (PurSequenceDerivedAdjoints l E W S O) := by
  obtain ⟨RP, η, sRP, hRP, hη, hc⟩ :=
    SequenceKInjectiveComparison.sequenceKInjectiveComparisonShifts l E W F hl
      (W ↘ Spec (.of F.k)) S hS
  let := sRP
  obtain ⟨_, κ, hκ, _⟩ := hc
  obtain ⟨A, hA⟩ := purSequenceComparisonTranspose l E W F hl S hS O H RP η κ hκ.1
  let γ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex O.limit (.up ℤ))
    DerivedCategory.Q
  let ρ : O.p.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W :=
    γ.hom ≫ η ≫ Functor.whiskerLeft DerivedCategory.Q κ.hom
  have hρ : (coefficientSequenceLimit l E W).IsRightDerivedFunctor ρ
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ)) := by
    let := hRP
    have hu := Functor.IsRightDerivedFunctor.isLeftKanExtension RP η
      (HomologicalComplex.quasiIso (coefficientSequenceModules l E W) (.up ℤ))
    refine ⟨(Functor.isLeftKanExtension_iff_of_iso₂ η ρ γ.symm κ ?_).mp hu⟩
    simp only [ρ, Iso.symm_hom, Iso.inv_hom_id_assoc]
  refine ⟨{
    L := S.reduction
    R := coefficientSequenceLimit l E W
    ε := A.reductionCounit
    η := ρ
    left_derived := A.reductionUniversal
    right_derived := hρ
    adjunction := S.adjunction
    left := Iso.refl _
    right := Iso.refl _
    left_model := ?_
    right_model := ?_
    hom_normalization := ?_
    unit := ?_
    counit := ?_
    model := fun N J j ↦ SequenceKInjectiveComparison.replacementIso l E W N J j
    model_eq := ?_
    composition_model := ?_ }⟩
  · intro Q hQ hf
    obtain ⟨e, he, hp⟩ := A.representative Q hQ hf
    exact ⟨e, by simpa using he, hp⟩
  · intro I hi
    let := hi
    have := hη I
    dsimp only [ρ, NatTrans.comp_app, Functor.whiskerLeft_app]
    infer_instance
  · intro Q I f
    simpa only [ρ, γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc] using
      hA Q I f
  · intro P
    simp
  · intro N
    simp
  · intro N J j hJ hj
    apply heq_of_eq
    dsimp only [SequenceKInjectiveComparison.replacementIso,
      SequenceKInjectiveComparison.restrictionFactors, purSequenceTowerLimitModel]
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
  · intro I hi J hJ j hj
    have hh := hκ.1.2 I J j
    refine ⟨hh.1, ?_⟩
    dsimp only [ρ, γ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [Iso.refl_hom]
    change (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex O.limit (.up ℤ)).hom.app I) ≫
        η.app I ≫ κ.hom.app (DerivedCategory.Q.obj I)) ≫ 𝟙 _ ≫
          (SequenceKInjectiveComparison.replacementIso l E W I J j).hom = _
    simpa only [Category.id_comp, Category.assoc,
      SequenceKInjectiveComparison.replacementIso, SequenceKInjectiveComparison.comparisonIso,
      SequenceKInjectiveComparison.restrictionFactors, SequenceKInjectiveComparison.limitComplex,
      coefficientConstantTowerLimit]
      using congrArg
      (DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex O.limit (.up ℤ)).hom.app I) ≫ ·) hh.2

end WeilConjectures
