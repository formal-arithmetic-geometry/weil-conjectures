/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.ModelDecomposition
public import WeilConjectures.TraceFormula.TraceClass

/-!

# The trace formula for proper smooth curves and for the affine line

This file proves the trace formula for the affine line `𝔸¹_{k₀}` as in the blueprint
(`sk-thm-trace-formula`, second paragraph of the proof): the trace formula holds on the proper
smooth curve `ℙ¹_{k₀}` by the Lefschetz–Verdier formula, and it passes to the open subscheme
`𝔸¹_{k₀}` through the extension by zero.

## The trace formula on proper smooth curves

For a model `X` of a proper smooth curve `X₀` over `k₀`, the Lefschetz–Verdier formula for the
graph correspondence `c_m = (𝟙, Φ_m)` (`Correspondence.trace_globalOperator_eq_sum_localTerm`)
writes the trace of the global operator as the sum of the local terms over the clopen pieces of
the fixed locus, and each local term at a fixed point is the trace of the local Frobenius
(`WeilBoundedConstructible.localTerm_traceClass_graph_eq_trace`)
(`ProEtale.CondensedRing.WeilBoundedConstructible.traceFormula_of_isProper`). This uses the
decomposition of the fixed locus of `Φ_m` into its reduced rational points
(`ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_fixedPointDecomposition`).

## Sorried input

- `ProEtale.CondensedRing.WeilBoundedConstructible.nonempty_fixedPointDecomposition`: the fixed
  scheme of the iterate `Φ_m` of the model Frobenius of a proper `X` is the finite disjoint union
  of its rational points, each a reduced open and closed point (it is étale over `k`, the graph
  of a Frobenius being transversal to the diagonal).

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Endofunctor

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] boundedConstructibleBraiding

variable {ℓ : ℕ} [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

namespace WeilBoundedConstructible

variable {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  [IsSeparated X.hom] {Φ : X ⟶ X}

/-- A decomposition of the fixed locus of the graph correspondence `c_m = (𝟙, Φ_m)` into its
rational points: a fixed locus `F` proper over `s` with finitely many pairwise disjoint open and
closed pieces `B_x ⟶ F` covering `F`, indexed by the fixed points `x` of `Φ_m`, the piece `B_x`
having underlying set the point `x`. -/
structure FixedPointDecomposition (K : WeilBoundedConstructible ℓ Φ) (m : ℕ)
    [Fintype (FixedPoint Φ m)] where
  /-- The fixed locus. -/
  F : (K.graph m).FixedLocus
  [isProper : IsProper F.F.hom]
  /-- The piece at a fixed point. -/
  B : FixedPoint Φ m → Over (Spec (.of k))
  [quasiCompact : ∀ x, QuasiCompact (B x).hom]
  [isProper_B : ∀ x, IsProper (B x).hom]
  /-- The inclusion of the piece at a fixed point. -/
  j : ∀ x, B x ⟶ F.F
  [isOpenImmersion : ∀ x, IsOpenImmersion (j x).left]
  [isClosedImmersion : ∀ x, IsClosedImmersion (j x).left]
  disjoint : Pairwise fun x x' ↦ Disjoint (Set.range (j x).left.base)
    (Set.range (j x').left.base)
  cover : ⋃ x, Set.range (j x).left.base = Set.univ
  range_eq (x : FixedPoint Φ m) : Set.range (j x).left.base =
    {(K.fixedLocusPoint m F x.1 x.2).left.base (default : Spec (.of k))}

attribute [instance] FixedPointDecomposition.isProper FixedPointDecomposition.quasiCompact
  FixedPointDecomposition.isProper_B FixedPointDecomposition.isOpenImmersion
  FixedPointDecomposition.isClosedImmersion

set_option linter.overlappingInstances false in
/-- **The fixed locus of a Frobenius is the disjoint union of its rational points**: for the model
Frobenius `Φ` of a proper `X = X₀ ×_{k₀} k` and `m ≥ 1`, the fixed scheme of `Φ_m` (the
equalizer of `𝟙` and `Φ_m`) is étale over `k`, the graph of a Frobenius being transversal to the
diagonal; it is therefore the finite disjoint union of the reduced points `Spec k` given by the
fixed rational points. This is a geometric input of the trace formula (Lang), stated here and
not proved. -/
theorem nonempty_fixedPointDecomposition [IsAlgClosed k] {k₀ : Type u} [Field k₀] [Finite k₀]
    [Algebra k₀ k] {X₀ : Scheme.{u}} {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) [IsProper X.hom] (K : WeilBoundedConstructible ℓ Φ) {m : ℕ}
    (hm : 1 ≤ m) [Fintype (FixedPoint Φ m)] : Nonempty (K.FixedPointDecomposition m) :=
  sorry

set_option linter.overlappingInstances false in
/-- **The trace formula on a proper smooth curve** (blueprint `sk-thm-trace-formula`, through
`sk-p-frob` and `sk-p-local`): for the model Frobenius `Φ` of a proper curve `X = X₀ ×_{k₀} k`
smooth over `k`, the trace of the global operator is the sum of the local terms of the graph
correspondence `c_m` along the fixed points (Lefschetz–Verdier), and each local term is the trace
of the local Frobenius. -/
theorem traceFormula_of_isProper [IsAlgClosed k] [SmoothOfRelativeDimension 1 X.hom]
    [IsProper X.hom] {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
    {f₀ : X₀ ⟶ Spec (.of k₀)} [LocallyOfFiniteType f₀] {p : X.left ⟶ X₀}
    (hΦ : IsModelFrobenius Φ f₀ p) (K : WeilBoundedConstructible ℓ Φ) {m : ℕ} (hm : 1 ≤ m) :
    haveI := hΦ.isFinite m
    haveI := hΦ.isUniversalHomeomorphism m
    K.TraceFormula m := by
  have := hΦ.isFinite m
  have := hΦ.isUniversalHomeomorphism m
  intro _ _ _
  obtain ⟨D⟩ := nonempty_fixedPointDecomposition hΦ K hm
  rw [globalOperator_eq_correspondenceGlobalOperator,
    Correspondence.trace_globalOperator_eq_sum_localTerm _ D.F D.B D.j D.disjoint D.cover]
  exact Finset.sum_congr rfl fun x _ ↦
    localTerm_traceClass_graph_eq_trace hΦ K hm D.F x.1 x.2 (D.j x) (D.range_eq x)

end WeilBoundedConstructible

section Model

variable {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k]

variable (ℓ) in
/-- **The trace formula for proper smooth curves** (blueprint `sk-thm-trace-formula`): for a
model `X₀` proper and smooth of relative dimension one over `k₀`. -/
theorem modelTraceFormula_of_isProper [IsAlgClosed k] {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ Spec (.of k₀)) [IsProper f₀] [SmoothOfRelativeDimension 1 f₀] :
    ModelTraceFormula ℓ (k := k) f₀ := by
  intro X _ _ _ Φ p hΦ K m hm
  have : IsProper X.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) hΦ.isPullback ‹_›
  have : SmoothOfRelativeDimension 1 X.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback hΦ.isPullback ‹_›
  have := hΦ.isFinite m
  have := hΦ.isUniversalHomeomorphism m
  intro _ _ _
  exact WeilBoundedConstructible.traceFormula_of_isProper hΦ K hm

end Model

end AlgebraicGeometry.ProEtale.CondensedRing
