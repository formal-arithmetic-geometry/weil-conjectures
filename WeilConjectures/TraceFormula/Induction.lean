/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.OpenClosedInduction
public import WeilConjectures.TraceFormula.Fibration

/-!

# The trace formula over every model

The trace formula over every separated model of finite type
(`ProEtale.CondensedRing.modelTraceFormula`,
blueprint `sk-thm-trace-formula`), by induction from the dimension zero and curve cases:

1. closed subschemes of the affine line `𝔸¹_{k₀}`: the line itself is smooth of relative dimension
   one, a proper closed subscheme is finite;
2. closed subschemes of `𝔸ⁿ_{k₀}`, by induction on `n` through the projection `𝔸ⁿ ⟶ 𝔸ⁿ⁻¹`, whose
   fibres over `k₀`-points are closed subschemes of `𝔸¹_{k₀}`
   (`ModelTraceFormulaOne.of_fibration`), in degree one and over all finite fields `k₀ ⊆ k`;
3. affine models, through a presentation, in all degrees
   (`modelTraceFormula_of_modelTraceFormulaOne`);
4. all models of finite type, by induction along open–closed decompositions
   (`modelTraceFormula_of_isCompl`, `AlgebraicGeometry.Scheme.induction_on_isCompl`).

The Grothendieck–Lefschetz trace formula and the point-counting formula follow.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-- `Spec` of a finite type algebra is locally of finite type. -/
lemma locallyOfFiniteType_specMap_algebraMap (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

section Model

variable (ℓ) in
/-- **The degree one trace formula over the closed subschemes of affine spaces** (blueprint
`sk-thm-trace-formula`), over every finite field `k₀ ⊆ k`, by induction on the number of
variables. -/
theorem modelTraceFormulaOne_mvPolynomial [IsAlgClosed k] (n : ℕ) :
    ∀ (k₀ : Type u) [Field k₀] [Finite k₀] [Algebra k₀ k]
      (I : Ideal (MvPolynomial (Fin n) k₀)),
      haveI := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin n) k₀ ⧸ I)
      ModelTraceFormulaOne ℓ (k := k)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin n) k₀ ⧸ I)))) := by
  have one (k₀ : Type u) [Field k₀] [Finite k₀] [Algebra k₀ k]
      (J : Ideal (MvPolynomial (Fin 1) k₀)) :
      haveI := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J)
      ModelTraceFormulaOne ℓ (k := k)
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J)))) := by
    have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J)
    by_cases hJ : J = ⊥
    · subst hJ
      have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin 1) k₀)
      have := smoothOfRelativeDimension_spec_mvPolynomial_fin_one (k₀ := k₀)
      exact ModelTraceFormulaOne.of_iso (ModelTraceFormulaOne.of_modelTraceFormula
        (modelTraceFormula_of_smoothOfRelativeDimension_one _))
        specMvPolynomialQuotientBotIso specMvPolynomialQuotientBotIso_hom_comp
    · have := isFinite_spec_mvPolynomial_fin_one_quotient hJ
      exact ModelTraceFormulaOne.of_modelTraceFormula (modelTraceFormula_of_isFinite _)
  induction n with
  | zero =>
    intro k₀ _ _ _ I
    have := isFinite_spec_mvPolynomial_fin_zero_quotient I
    exact ModelTraceFormulaOne.of_modelTraceFormula (modelTraceFormula_of_isFinite _)
  | succ n ih =>
    intro k₀ _ _ _ I
    rcases n with _ | n
    · exact one k₀ I
    · have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin (n + 2)) k₀ ⧸ I)
      have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin (n + 1)) k₀)
      have := locallyOfFiniteType_specMap_algebraMap k₀
        (MvPolynomial (Fin (n + 1)) k₀ ⧸ (⊥ : Ideal (MvPolynomial (Fin (n + 1)) k₀)))
      have : LocallyOfFiniteType (mvPolynomialQuotientProjection I) := by
        have h := mvPolynomialQuotientProjection_comp I
        have : LocallyOfFiniteType (mvPolynomialQuotientProjection I ≫
            Spec.map (CommRingCat.ofHom (algebraMap k₀ (MvPolynomial (Fin (n + 1)) k₀)))) := by
          rw [h]
          infer_instance
        exact locallyOfFiniteType_of_comp _ (Spec.map (CommRingCat.ofHom
          (algebraMap k₀ (MvPolynomial (Fin (n + 1)) k₀))))
      refine ModelTraceFormulaOne.of_fibration (mvPolynomialQuotientProjection I)
        (mvPolynomialQuotientProjection_comp I)
        (ModelTraceFormulaOne.of_iso (ih k₀ ⊥) (specIsoOfAlgEquiv (AlgEquiv.quotientBot k₀ _))
          (specIsoOfAlgEquiv_hom_comp _)) fun y₀ hy₀ ↦ ?_
      obtain ⟨J, e, he⟩ := exists_iso_pullback_mvPolynomialQuotientProjection I y₀ hy₀
      have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin 1) k₀ ⧸ J)
      exact ModelTraceFormulaOne.of_iso (one k₀ J) e he

/-- The degree one trace formula over affine models. -/
theorem modelTraceFormulaOne_of_isAffine [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] : ModelTraceFormulaOne ℓ (k := k) f₀ := by
  obtain ⟨n, I, e, he⟩ := exists_iso_spec_mvPolynomial_quotient f₀
  have := locallyOfFiniteType_specMap_algebraMap k₀ (MvPolynomial (Fin n) k₀ ⧸ I)
  exact ModelTraceFormulaOne.of_iso (modelTraceFormulaOne_mvPolynomial ℓ n k₀ I) e he

/-- The trace formula over affine models (blueprint `sk-thm-trace-formula`). -/
theorem modelTraceFormula_of_isAffine [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀]
    [LocallyOfFiniteType f₀] : ModelTraceFormula ℓ (k := k) f₀ :=
  modelTraceFormula_of_modelTraceFormulaOne fun k₁ _ _ _ _ _ ↦
    modelTraceFormulaOne_of_isAffine (modelFieldChange f₀ k₁)

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

/-- **The trace formula over every model** (blueprint `sk-thm-trace-formula`), by Noetherian
induction from `modelTraceFormula_of_isCompl`, `modelTraceFormula_of_isFinite`,
`modelTraceFormula_of_smoothOfRelativeDimension_one` and the fibration step of
`nonempty_weilCompactCohomology_weilLowerShriekOfFrobenius_iso` and
`nonempty_weilStalk_weilLowerShriekOfFrobenius_iso`. -/
theorem modelTraceFormula [IsAlgClosed k] {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀))
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀] :
    ModelTraceFormula ℓ (k := k) f₀ := by
  have := QuasiCompact.compactSpace_of_compactSpace f₀
  refine Scheme.induction_on_isCompl
    (fun {X₀} (f : X₀ ⟶ Spec (.of k₀)) ↦ ∀ [LocallyOfFiniteType f], ModelTraceFormula ℓ (k := k) f)
    (fun f hX _ ↦ ?_) (fun f j i _ _ _ _ hcompl hU hZ _ ↦ ?_) f₀
  · have := hX
    exact modelTraceFormula_of_isAffine f
  · exact modelTraceFormula_of_isCompl f j i hcompl hU hZ

end Model

/-! ### The trace formula -/

variable {Φ : X ⟶ X} {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}


/-- **The Grothendieck–Lefschetz trace formula** (blueprint
`thm-trf-grothendieck-lefschetz-finite-ring`, `thm-trf-grothendieck-lefschetz-qbar`): let
`X = X₀ ×_{k₀} k` be the base change of a separated `k₀`-scheme of finite type to an
algebraically closed field `k`, with model Frobenius `Φ`, and let `(K, φ)` be a Weil object of
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧` for `Φ`. For every `m ≥ 1`,
```
tr(F_{c,m} | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(F_{x,m} | K_x̄),
```
the sum running over the rational points `x` of `X` fixed by `Φ_m`, where `F_{c,m}` is the
Frobenius of the compactly supported cohomology `RΓ_c(X, (K, φ_m))` and `F_{x,m}` the Frobenius
of the stalk of `(K, φ_m)` at `x`, both Weil objects for the identity of the base point. -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius [IsAlgClosed k] [IsSeparated f₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    trace (K.globalOperator m) = ∑ x : FixedPoint Φ m, trace (K.stalkFrobenius m x.1 x.2) := by
  have h := modelTraceFormula (ℓ := ℓ) (k := k) f₀ X Φ p hΦ K m hm
  exact h

/-- **The Grothendieck–Lefschetz trace formula in `ℚ̄_ℓ`**: the trace formula
`trace_globalOperator_eq_sum_trace_stalkFrobenius` read through
`End (ℚ̄_ℓ,s) ≅ ℚ̄_ℓ` (`unitEndRingEquiv`). -/
theorem trace_globalOperator_eq_sum_trace_stalkFrobenius_padicAlgCl [IsAlgClosed k]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ) (m : ℕ) (hm : 1 ≤ m)
    [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    unitEndRingEquiv ℓ k (trace (K.globalOperator m)) =
      ∑ x : FixedPoint Φ m, unitEndRingEquiv ℓ k (trace (K.stalkFrobenius m x.1 x.2)) := by
  rw [trace_globalOperator_eq_sum_trace_stalkFrobenius hΦ K m hm, map_sum]

/-- **Counting points** (blueprint `cor-trf-point-counting`): the trace of the global operator
`F_{c,m}` on `RΓ_c(X, ℚ̄_ℓ)` is the number of points of `X₀` rational over `𝔽_{q^m}`, the
number of rational points of `X` fixed by `Φ_m`. -/
theorem trace_globalOperator_unit_eq_card [IsAlgClosed k] [IsSeparated f₀]
    [LocallyOfFiniteType f₀] [QuasiCompact f₀] (hΦ : IsModelFrobenius Φ f₀ p) (m : ℕ)
    (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (WeilBoundedConstructible.unit ℓ Φ).carrier)] :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    trace ((WeilBoundedConstructible.unit ℓ Φ).globalOperator m) =
      (Fintype.card (FixedPoint Φ m) :
        End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) := by
  have : ∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        (WeilBoundedConstructible.unit ℓ Φ).carrier) := fun x ↦
    (WeilBoundedConstructible.nonempty_hasRightDual_stalk _ x).some
  rw [trace_globalOperator_eq_sum_trace_stalkFrobenius hΦ _ m hm]
  simp only [WeilBoundedConstructible.trace_stalkFrobenius_unit, Finset.sum_const,
    Finset.card_univ]
  exact nsmul_one (A := End (𝟙_ (Dᵇc((point k).left)⟦Profinite.padicAlgClRingObj ℓ⟧))) _

end AlgebraicGeometry.ProEtale.CondensedRing
