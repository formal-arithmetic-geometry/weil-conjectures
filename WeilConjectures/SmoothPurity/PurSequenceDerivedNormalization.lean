/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Pur.PurSequenceAdjointResolutionData
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.PurSequenceOrdinaryModel
import WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitRestrictionAcyclicity
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitDerivedAdjunctionComparison
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitCanonicalModels
import all WeilConjectures.TraceFormula.CompletionUnit.CompletionUnitFixedCalculusModels

/-! # Assembly of the normalized derived projection data

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`, coefficient-comparison paragraph, via the original
sequence-projection normalization proof steps
(blueprint: lem-pur-sequence-derived-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe t u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

set_option linter.unusedVariables false in
/--
The supplied finite-field coefficient calculus and ordinary ringed projection admit the
normalized derived adjoint data.  The fields of `PurSequenceDerivedAdjoints` record the
universal left and right derived comparisons, their strict K-flat and K-injective models,
the adjunction unit and counit normalizations, and the canonical comparison for every
simultaneous tower replacement.

Source: `literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`, coefficient-comparison paragraph, via the original
sequence-projection normalization proof steps.  The statement packages the following
steps: (1) obtain the universal K-injective comparison, its map to total inverse limit,
and the compatible K-flat comparison; (2) identify the left comparison with the supplied
reduction and the right comparison with the ordinary limit identification followed by
those universal comparisons; (3) transport the adjunction, unit, counit, and
Hom-normalization equations along these identifications; and (4) use the arbitrary
replacement isomorphism and functoriality to obtain the model equality and the normalized
`lim (j)` composition equation.  These are the clauses represented by the returned
`PurSequenceDerivedAdjoints` structure.
(blueprint: lem-pur-sequence-derived-normalization).
-/
theorem purSequenceDerivedNormalization
    (F : FiniteFieldDatum.{t}) (hl : l ≠ F.p)
    [W.Over (Spec (.of F.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of F.k))] [QuasiCompact (W ↘ Spec (.of F.k))]
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S)
    (O : PurSequenceOrdinaryAdjoints l E W)
    (H : PurSequenceRingedFactorization l E W O) :
    Nonempty (PurSequenceDerivedAdjoints l E W S O) := by
  let c := CompletionUnit.termwiseLimitComparison l E W
  let M := CompletionUnit.ordinaryModelOfAdjoints l E W O c
    (CompletionUnit.termwiseLimitComparison_projection l E W)
  obtain ⟨hI, ε, hε, hflat, heval, hhom⟩ :=
    CompletionUnit.fixedDerivedComparison l E W S M c
      (CompletionUnit.termwiseLimitComparison_projection l E W)
      (CompletionUnit.constantLimitUnit l E W)
      (CompletionUnit.constantLimitUnit_normalization l E W)
  let δ := CompletionUnit.systemLimitUnit l E W M (CompletionUnit.constantLimitUnit l E W)
  let η : O.p.modules.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ coefficientSequenceLimit l E W :=
    Functor.whiskerRight (NatIso.mapHomologicalComplex O.limit (.up ℤ)).hom
      DerivedCategory.Q ≫ δ
  have hη (I : CochainComplex (coefficientSequenceModules l E W) ℤ) (hI' : I.IsKInjective) :
      IsIso (η.app I) := by
    have := hI I hI'
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app]
    infer_instance
  refine ⟨{
    L := S.reduction
    R := coefficientSequenceLimit l E W
    ε := ε
    η := η
    left_derived := hε
    right_derived := ?_
    adjunction := S.adjunction
    left := Iso.refl _
    right := Iso.refl _
    left_model := ?_
    right_model := hη
    hom_normalization := ?_
    unit := ?_
    counit := ?_
    model := fun N J j _ _ ↦ (coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app N ≪≫
        asIso (DerivedCategory.Q.map j)) ≪≫ purSequenceTowerLimitModel l E W J
    model_eq := fun _ _ _ _ _ ↦ HEq.rfl
    composition_model := ?_ }⟩
  · have : O.p.modules.Additive := Functor.additive_of_iso O.limit.symm
    exact (CategoryTheory.derives O.p.modules).isRightDerivedFunctor_of_isIso η
      (fun I ↦ hη I.obj I.property)
  · intro Q hQ hQflat
    have := hflat Q hQ hQflat
    refine ⟨asIso (ε.app Q), by simp, fun n ↦ heval Q hQ hQflat n, ?_⟩
    intro m n h
    unfold CoefficientTransitionEquation coefficientComplexCompositeTransformation
    ext i : 1
    exact O.tensor_transition (Q.X i) m n h
  · intro Q I f
    rw [hhom Q I f]
    dsimp only [η, NatTrans.comp_app, Functor.whiskerRight_app]
    rw [← Category.assoc, ← Functor.map_comp]
    congr 2
    ext i : 1
    (simp [M, CompletionUnit.ordinaryModelOfAdjoints, Adjunction.homEquiv_unit]; rfl)
  · intro P
    simp
  · intro N
    simp
  · intro I _ J _ j _
    refine ⟨CompletionUnit.restricted_limit_acyclic l E W I J j, ?_⟩
    have hn := CompletionUnit.constantLimitUnit_normalization l E W J
    have hnat := (CompletionUnit.constantLimitUnit l E W).naturality j
    dsimp only [η, δ, CompletionUnit.systemLimitUnit, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.refl_hom, NatTrans.id_app,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom, Functor.comp_map] at hnat ⊢
    simp only [Category.assoc]
    congr 1
    erw [Category.id_comp]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc, ← reassoc_of% hnat]
    erw [hn]
    simp only [M, CompletionUnit.ordinaryModelOfAdjoints, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, ← Functor.map_comp]
    congr 1
    simp [c]

end WeilConjectures
