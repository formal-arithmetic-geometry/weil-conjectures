/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.CoefficientMorphismAdditivity
public import WeilConjectures.TraceFormula.CoefficientMorphismProper
public import WeilConjectures.TraceFormula.CoefficientMorphismPushforward
public import WeilConjectures.TraceFormula.ModelExtension
public import WeilConjectures.TraceFormula.ModelOpenClosed
public import WeilConjectures.TraceFormula.ModelProjectiveImmersion

/-!

# The trace formula for Frobenius coefficient morphisms

Let `Φ` be the model Frobenius of `X = X₀ ×_{k₀} k`, `K` a bounded constructible complex on `X`
and `ψ : LΦ^* K ⟶ K` an arbitrary, not necessarily invertible, morphism (a *Frobenius
coefficient morphism*, blueprint `def-trf-frobenius-coefficient-morphism`), with iterates
`ψ_m : LΦ_m^* K ⟶ K` and global operators `F_{c,m}(ψ) = RΓ_c(X, ψ_m) ∘ Φ_m^♯`
(`ProEtale.CondensedRing.frobeniusCompactOperator`). The trace formula
```
tr(F_{c,m}(ψ) | RΓ_c(X, K)) = ∑_{x ∈ X₀(𝔽_{q^m})} tr(ψ_{m,x} | K_x)
```
(`ProEtale.CondensedRing.trace_frobeniusCompactOperator_eq_sum`, blueprint
`thm-trf-coefficient-morphism-trace-formula`) is the coefficient-morphism variant of the
Grothendieck–Lefschetz formula.

The proof follows the blueprint. The trace formula in degree `m` for `Φ` is the trace formula in
degree one (`ProEtale.CondensedRing.TraceFormulaHolds`) for the iterate `Φ_m`, the model
Frobenius of the base change of `X₀` to the extension of degree `m` of `k₀` (Step 0). It holds on
proper schemes by the Lefschetz–Verdier formula and the Frobenius local term
(`ProEtale.CondensedRing.traceFormulaHolds_of_isProper`, Step 2). An affine `X₀` embeds into a
projective space over `k₀`, and the trace formula passes along this immersion, whose fibres are
proper (`ProEtale.CondensedRing.traceFormulaHolds_of_isProper_pullback`, Steps 3–4). Finally a
finite affine open cover of `X₀` and the additivity of the trace along open–closed
decompositions (`ProEtale.CondensedRing.TraceFormulaHolds.of_isCompl`) give the general case
(Step 5).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

omit [Fact (ringChar k).Prime] in
/-- The model Frobenius is finite. -/
lemma IsModelFrobenius.isFinite_left {X : Over (Spec (.of k))} {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) : IsFinite Φ.left := by
  have := hΦ.isFinite 1
  rwa [frobeniusIterate_one] at this

omit [Fact (ringChar k).Prime] in
/-- The model Frobenius is a universal homeomorphism. -/
lemma IsModelFrobenius.isUniversalHomeomorphism_left {X : Over (Spec (.of k))} {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p) :
    IsUniversalHomeomorphism Φ.left := by
  have := hΦ.isUniversalHomeomorphism 1
  rwa [frobeniusIterate_one] at this

/-- The trace formula in degree one for a model Frobenius whose model is covered by `n` affine
opens, by induction on `n` (blueprint `thm-trf-coefficient-morphism-trace-formula`, Steps 2–5). -/
theorem traceFormulaHolds_of_card_eq [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] (n : ℕ) :
    ∀ {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
      [IsSeparated X.hom] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀]
      {p : X.left ⟶ X₀} {Φ : X ⟶ X} (_ : IsModelFrobenius Φ f₀ p) [IsProper Φ.left]
      {s : Finset X₀.Opens}, s.card = n → (∀ U ∈ s, IsAffineOpen U) → ⨆ U ∈ s, U = ⊤ →
        TraceFormulaHolds ℓ Φ := by
  induction n with
  | zero =>
    intro X _ _ _ X₀ f₀ _ p Φ hΦ _ s hs _ hcov
    have := isProper_hom_of_card_eq_zero p hs hcov
    exact traceFormulaHolds_of_isProper hΦ
  | succ n ih =>
    intro X _ _ _ X₀ f₀ _ p Φ hΦ _ s hs hsa hcov
    obtain ⟨U, _, _, _, Z, _, _, _, j, i, _, _, ΦU, ΦZ, U₀, fU₀, pU, Z₀, fZ₀, pZ, t, hj, hi,
      hcompl, _, _, hΦU, _, hΦZ, ht, hta, htcov⟩ := hΦ.exists_isCompl hs hsa hcov
    have := hΦ.isFinite_left
    have := hΦ.isUniversalHomeomorphism_left
    have := hΦU.isFinite_left
    have := hΦU.isUniversalHomeomorphism_left
    have := hΦZ.isFinite_left
    have := hΦZ.isUniversalHomeomorphism_left
    refine TraceFormulaHolds.of_isCompl hcompl hj hi ?_ (ih hΦZ ht hta htcov)
    obtain ⟨Y, _, _, _, Y₀, fY₀, pY, ΦY, f, f₀', _, _, hΦY, hf, hfp, h₀, hfib⟩ :=
      hΦU.exists_isProper_pullback
    have := hΦY.isFinite_left
    exact traceFormulaHolds_of_isProper_pullback hΦU hΦY hf hfp h₀ (fun y _ ↦ hfib y)
      (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h ↦ traceFormulaHolds_of_isProper h)
      (traceFormulaHolds_of_isProper hΦY)

/-- **The trace formula in degree one for a model Frobenius** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, the statement `TF(X₀, K, ψ, 1)`). -/
theorem traceFormulaHolds_of_isModelFrobenius [IsAlgClosed k] {X : Over (Spec (.of k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] {k₀ : Type u}
    [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] : TraceFormulaHolds ℓ Φ := by
  obtain ⟨s, hsa, hcov⟩ := hΦ.exists_finset_isAffineOpen
  exact traceFormulaHolds_of_card_eq s.card hΦ rfl hsa hcov

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom]

variable (ℓ) in
/-- **The trace formula for Frobenius coefficient morphisms** (blueprint
`thm-trf-coefficient-morphism-trace-formula`): for the model Frobenius `Φ` of a separated model
`X₀` of finite type over a finite field `k₀`, a bounded constructible `K` with an arbitrary map
`ψ : LΦ^* K ⟶ K` and `m ≥ 1`, the trace of `F_{c,m}(ψ)` on `RΓ_c(X, K)` is the sum over the
rational points `x` fixed by `Φ_m` of the traces of the stalk maps `ψ_{m,x}` on `K_x`. No
invertibility of `ψ` is assumed. -/
theorem trace_frobeniusCompactOperator_eq_sum [IsAlgClosed k] {k₀ : Type u} [Field k₀]
    [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)}
    [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀} {Φ : X ⟶ X} (hΦ : IsModelFrobenius Φ f₀ p)
    [IsProper Φ.left] (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧)
    (ψ : (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ Φ).obj K ⟶ K)
    {m : ℕ} (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)]
    [HasRightDual
      ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ (toPoint X)).obj K)]
    [∀ x : RationalPoint X,
      HasRightDual ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ x).obj K)] :
    trace (frobeniusCompactOperator ℓ ψ m) =
      ∑ x : FixedPoint Φ m, trace (Correspondence.graphStalkMap K (frobeniusIterate Φ m)
        (frobeniusCoefficientIterate ψ m) x.1 x.2) := by
  obtain ⟨k₁, _, _, _, _, _, hcard⟩ := exists_finiteField_natCard_eq_pow k₀ k (m := m) (by omega)
  exact (traceFormulaHolds_of_isModelFrobenius
    (hΦ.fieldChange (k₁ := k₁) hcard)).trace_frobeniusCompactOperator K ψ

end AlgebraicGeometry.ProEtale.CondensedRing
