/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.DegreeOne
public import WeilConjectures.TraceFormula.ModelExtension

/-!

# The trace formula in degree one over a model

The *degree one trace formula* of a Weil object `(K, φ)` for `Φ`
(`ProEtale.CondensedRing.WeilBoundedConstructible.TraceFormulaOne`) is
```
tr(F_c | RΓ_c(X, K)) = ∑_{x fixed by Φ} tr(φ_x | K_x̄),
```
stated with the compactly supported Frobenius of `(K, φ)` and the Frobenii of its stalks, no
iterate being taken. Over a model `X₀` it is `ProEtale.CondensedRing.ModelTraceFormulaOne`.

* The trace formula in degree `m` for `(K, φ)` is the degree one trace formula of the iterate
  `(K, φ_m)` for `Φ_m` (`WeilBoundedConstructible.traceFormula_of_traceFormulaOne_iterate`).
* `Φ_m` is the model Frobenius of the base change of `X₀` to the subfield `𝔽_{q^m}` of `k`
  (`IsModelFrobenius.fieldChange`), so the degree one trace formula over all finite subfields
  gives the trace formula in all degrees (`modelTraceFormula_of_modelTraceFormulaOne`, blueprint
  `sk-thm-trace-formula`: "the induction must range over all finite extensions").
* The degree one trace formula over a model is invariant under isomorphisms of models
  (`ModelTraceFormulaOne.of_iso`) and follows from the trace formula
  (`ModelTraceFormulaOne.of_modelTraceFormula`).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

/-- The conjugate of a `q`-power Frobenius by an isomorphism is a `q`-power Frobenius. -/
lemma Scheme.Hom.IsFrobenius.conj {X₀ Y₀ : Scheme.{u}} {F : X₀ ⟶ X₀} {q : ℕ}
    (hF : F.IsFrobenius q) (e : X₀ ≅ Y₀) : (e.inv ≫ F ≫ e.hom).IsFrobenius q := by
  intro R t φ hφ
  rw [← Category.assoc, ← Category.assoc, hF (t ≫ e.inv) φ hφ]
  simp

end AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

/-! ### Models -/

section Model

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- The model Frobenius is finite. -/
lemma IsModelFrobenius.isFinite_self [LocallyOfFiniteType f₀] (hΦ : IsModelFrobenius Φ f₀ p) :
    IsFinite Φ.left := by
  have h := hΦ.isFinite 1
  rwa [frobeniusIterate_one] at h

/-- The model Frobenius is a universal homeomorphism. -/
lemma IsModelFrobenius.isUniversalHomeomorphism_self (hΦ : IsModelFrobenius Φ f₀ p) :
    IsUniversalHomeomorphism Φ.left := by
  have h := hΦ.isUniversalHomeomorphism 1
  rwa [frobeniusIterate_one] at h

omit [Finite k₀] in
/-- A model of `X₀` is a model of every `Y₀ ≅ X₀` over `k₀`. -/
lemma IsModelFrobenius.ofIso (hΦ : IsModelFrobenius Φ f₀ p) {Y₀ : Scheme.{u}}
    {g₀ : Y₀ ⟶ Spec (.of k₀)} (e : X₀ ≅ Y₀) (he : e.hom ≫ g₀ = f₀) :
    IsModelFrobenius Φ g₀ (p ≫ e.hom) where
  isPullback := by
    have h := hΦ.isPullback.paste_horiz
      (IsPullback.of_horiz_isIso (fst := e.hom) (snd := f₀) (f := g₀)
        (g := 𝟙 (Spec (.of k₀))) ⟨by rw [he, Category.comp_id]⟩)
    rwa [Category.comp_id] at h
  exists_isFrobenius := by
    obtain ⟨F₀, hF₀, hp⟩ := hΦ.exists_isFrobenius
    exact ⟨e.inv ≫ F₀ ≫ e.hom, hF₀.conj e, by simp [reassoc_of% hp]⟩

end Model

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]

namespace WeilBoundedConstructible

/-! ### The degree one trace formula -/

variable (K) in
/-- The *degree one trace formula* for a Weil object `(K, φ)` for `Φ`: the trace of the
compactly supported Frobenius of `(K, φ)` is the sum, over the rational points `x` fixed by `Φ`,
of the traces of the Frobenii of the stalks `K_x̄`, for any choice of duals. -/
def TraceFormulaOne {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ) [IsFinite Φ.left]
    [IsUniversalHomeomorphism Φ.left] : Prop :=
  ∀ [Fintype {x : RationalPoint X // x ≫ Φ = x}]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        K.carrier)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        K.carrier)],
    trace K.compactFrobenius =
      ∑ x : {x : RationalPoint X // x ≫ Φ = x}, trace (K.weilStalkFrobenius x.1 x.2)

/-- The trace formula in degree `m` is the degree one trace formula of the iterate `(K, φ_m)`. -/
theorem traceFormula_of_traceFormulaOne_iterate {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)
    (m : ℕ) [IsFinite (frobeniusIterate Φ m).left]
    [IsUniversalHomeomorphism (frobeniusIterate Φ m).left] (h : (K.iterate m).TraceFormulaOne) :
    K.TraceFormula m := by
  intro _ iX iS
  let iXm : HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj
        (K.iterate m).carrier) := by
    rw [iterate_carrier]
    exact iX
  let iSm (x : RationalPoint X) : HasRightDual
      ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj
        (K.iterate m).carrier) := by
    rw [iterate_carrier]
    exact iS x
  have h' := @h _ iXm iSm
  rw [trace_globalOperator_eq K m (hK := iX) (hKm := iXm), h']
  exact Finset.sum_congr rfl fun x _ ↦ (trace_stalkFrobenius_eq K m x.1 x.2).symm

/-- The trace formula in degree one gives the degree one trace formula. -/
theorem traceFormulaOne_of_traceFormula_one {Φ : X ⟶ X} (K : WeilBoundedConstructible ℓ Φ)
    [IsFinite Φ.left] [IsUniversalHomeomorphism Φ.left]
    [IsFinite (frobeniusIterate Φ 1).left] [IsUniversalHomeomorphism (frobeniusIterate Φ 1).left]
    (h : K.TraceFormula 1) : K.TraceFormulaOne := by
  intro iF iX iS
  let e : FixedPoint Φ 1 ≃ {x : RationalPoint X // x ≫ Φ = x} :=
    Equiv.subtypeEquivRight fun x ↦ by rw [frobeniusIterate_one]
  let _ : Fintype (FixedPoint Φ 1) := Fintype.ofEquiv _ e.symm
  have h' := @h _ iX iS
  rw [← trace_globalOperator_one K, h']
  exact Fintype.sum_equiv e _ _ fun x ↦ trace_stalkFrobenius_one K x.1 x.2 (e x).2

end WeilBoundedConstructible

/-! ### The degree one trace formula over a model -/

section Model

variable (ℓ) {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

/-- The degree one trace formula over a model `X₀` of finite type over `k₀`: for every base change
`X` of `X₀` to `k` with its model Frobenius `Φ` and every Weil object `(K, φ)` for `Φ`, the degree
one trace formula holds (`WeilBoundedConstructible.TraceFormulaOne`). -/
def ModelTraceFormulaOne {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (.of k₀)) [LocallyOfFiniteType f₀] :
    Prop :=
  ∀ (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsSeparated X.hom] (Φ : X ⟶ X) (p : X.left ⟶ X₀) (hΦ : IsModelFrobenius Φ f₀ p)
    (K : WeilBoundedConstructible ℓ Φ),
      haveI := hΦ.isFinite_self
      haveI := hΦ.isUniversalHomeomorphism_self
      K.TraceFormulaOne

variable {ℓ}

/-- The degree one trace formula over a model is invariant under isomorphisms of models. -/
theorem ModelTraceFormulaOne.of_iso {X₀ Y₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    {g₀ : Y₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] [LocallyOfFiniteType g₀]
    (h : ModelTraceFormulaOne ℓ (k := k) g₀) (e : X₀ ≅ Y₀) (he : e.hom ≫ g₀ = f₀) :
    ModelTraceFormulaOne ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K
  exact h X Φ (p ≫ e.hom) (hΦ.ofIso e he) K

/-- The trace formula over a model gives the degree one trace formula. -/
theorem ModelTraceFormulaOne.of_modelTraceFormula {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] (h : ModelTraceFormula ℓ (k := k) f₀) :
    ModelTraceFormulaOne ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K
  have := hΦ.isFinite_self
  have := hΦ.isUniversalHomeomorphism_self
  have := hΦ.isFinite 1
  have := hΦ.isUniversalHomeomorphism 1
  intro _ _ _
  exact K.traceFormulaOne_of_traceFormula_one (h X Φ p hΦ K 1 le_rfl)

/-- **Reduction to degree one** (blueprint `sk-thm-trace-formula`): if the degree one trace
formula holds over the base change of `X₀` to every finite extension `k₁ ⊆ k` of `k₀`, then the
trace formula holds over `X₀` in every degree `m ≥ 1`, the iterate `Φ_m` being the model
Frobenius of the base change of `X₀` to the subfield `𝔽_{q^m}` of `k`. -/
theorem modelTraceFormula_of_modelTraceFormulaOne [IsAlgClosed k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
    (h : ∀ (k₁ : Type u) [Field k₁] [Finite k₁] [Algebra k₀ k₁] [Algebra k₁ k]
      [IsScalarTower k₀ k₁ k], ModelTraceFormulaOne ℓ (k := k) (modelFieldChange f₀ k₁)) :
    ModelTraceFormula ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K m hm
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ :=
    exists_finiteField_natCard_eq_pow k₀ k (m := m) (by omega)
  have hΦ' := hΦ.fieldChange hcard
  have := hΦ.isFinite m
  have := hΦ.isUniversalHomeomorphism m
  intro _ _ _
  exact K.traceFormula_of_traceFormulaOne_iterate m
    (h k₁ X (frobeniusIterate Φ m) _ hΦ' (K.iterate m))

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
