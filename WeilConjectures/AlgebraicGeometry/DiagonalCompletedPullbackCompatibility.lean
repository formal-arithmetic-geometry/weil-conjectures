/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficientPullback

import WeilConjectures.AlgebraicGeometry.DiagonalCompletedClassPullback
import WeilConjectures.AlgebraicGeometry.DiagonalCompletedTracePullback

/-! # Completed diagonal base change before scalar extension

Source: diagonal coefficient changes, paragraph (3).
(blueprint: lem-diagonal-completed-pullback-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance] completedRealization_shiftedLine_isIso

private theorem realizedTrace_eq (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}} (f : X ⟶ S)
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (R : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (square : CompletedPushSquare l f eX eS t.Rc R)
    (trace : R.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (htrace : CompletedTraceCompatibility l f eX eS t R square trace) :
    inv (R.R.map (eX.shiftedLine l X)) ≫ square.derived.iso.inv.app _ ≫
      eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S = trace := by
  have heq := htrace
  dsimp only [CompletedTraceCompatibility] at heq
  rw [heq]
  simp only [Iso.inv_hom_id_app_assoc, IsIso.inv_hom_id_assoc]

private theorem tracePullback_of_realized (l : ℕ) [Fact l.Prime]
    {X S X' S' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian S] [IsNoetherian X'] [IsNoetherian S']
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    [DiagonalTraceLocalizations l X'] [DiagonalTraceLocalizations l S']
    (f : X ⟶ S) (f' : X' ⟶ S') (hX : X' ⟶ X) (hS : S' ⟶ S)
    (square : IsPullback hX f' f hS)
    (hunit : IsUnit (l : Γ(S, ⊤))) (hunit' : IsUnit (l : Γ(S', ⊤)))
    (eX : CompletedRealization l X) (eS : CompletedRealization l S)
    (eX' : CompletedRealization l X') (eS' : CompletedRealization l S')
    (t : DiagonalTrace.Result l (ULift.{u} (Padic l)) f)
    (t' : DiagonalTrace.Result l (ULift.{u} (Padic l)) f')
    (D : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f))
    (D' : DiagonalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f'))
    (canonical : D.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f)
    (canonical' : D'.R = derivedLower (Profinite.continuousMapRingObj.{u} ℤ_[l]) f')
    (hcanonical : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f) D canonical)
    (hcanonical' : IsCanonicalRightDerived
      (CondensedRing.lowerStar (Profinite.continuousMapRingObj.{u} ℤ_[l]) f') D' canonical')
    (push : CompletedPushSquare l f eX eS t.Rc D)
    (push' : CompletedPushSquare l f' eX' eS' t'.Rc D')
    (line : PullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hX
      (zlLine l X) (zlLine l X') (spIntegralComparison hX l (bottomField l)))
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS)
    (trace : D.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X) 0).obj
        (zlLine l X))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S)
    (trace' : D'.R.obj (((DerivedCategory.singleFunctor
      (Modules (Profinite.continuousMapRingObj.{u} ℤ_[l]) X') 0).obj
        (zlLine l X'))⟦(2 : ℤ)⟧) ⟶ unit (Profinite.continuousMapRingObj.{u} ℤ_[l]) S')
    (htrace : CompletedTraceCompatibility l f eX eS t D push trace)
    (htrace' : CompletedTraceCompatibility l f' eX' eS' t' D' push' trace') :
    TracePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) f f' hX hS square.w.symm
      D D' canonical canonical' line c trace trace' := by
  have ht := diagonalCompletedTrace_pullback l f f' hX hS square hunit hunit'
    eX eS eX' eS' t t' D D' canonical canonical' hcanonical hcanonical' push push' line c
  dsimp only at ht
  rw [realizedTrace_eq l _ _ _ _ _ _ _ htrace,
    realizedTrace_eq l _ _ _ _ _ _ _ htrace'] at ht
  exact ht

private theorem firstProjection_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (baseW g)
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) (baseP g) := by
  exact IsPullback.paste_twist_right
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
    (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)).flip
    (ProjectiveLine Y' ↘ Y') (baseP g)
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (IsPullback.of_hasPullback (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y')).flip
    (by simp [baseW, baseP]) (by simp [baseW, baseP])

private theorem secondProjection_isPullback {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    IsPullback (baseW g)
      (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y)) (baseP g) := by
  exact IsPullback.paste_twist_right
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g)
    (IsPullback.of_hasPullback (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (ProjectiveLine Y' ↘ Y') (baseP g)
    (ProjectiveSpace.map_over (ULift.{u} (Fin 2)) g).symm
    (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (IsPullback.of_hasPullback (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
    (by simp [baseW, baseP]) (by simp [baseW, baseP])

/-- The completed diagonal class and the three completed traces commute with
geometric pullback after transport through their normalized Z_l references.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3), through the
base-changed decomposition, before applying the coefficient functors.
(blueprint: lem-diagonal-completed-pullback-compatibility).

Proof: Pull the positive Cartier roof along the displayed diagonal square:
units pull back by the units map and the inverse local equation pulls back to
the inverse pulled-back equation. The diagonal equation a-b and section
equation t remain regular after arbitrary base change. The quotient generator
therefore remains +1. Exact inverse image and the canonical tensor comparison
carry this to one morphism of the full Kummer systems, with multiplication by
ell in degree -1 and identity in degree zero. Closed-support base change
identifies the supported source. The normalized inverse-image/derived-limit
comparison is invertible on this source system and on the root-line system,
by the explicit coefficient limits and Cartesian root comparison. Naturality
of this comparison, applied to the whole roof, gives the completed class
square. Apply the same comparison to the entire unit/Chern splitting for each
of q, p1 and p2. Its two endpoint comparisons and its splitting maps are
invertible, so its base-change mate is invertible. Invert the commuting
splitting square and project to the constant summand; this gives each trace
square. Finally transport these equations by Reference.delta and the three
Reference trace equations. The normalization of all endpoints and the derived
universal units identifies these maps with sourcePullbackMap and modelExchange.
This uses the limit of the entire system, rather than detection of a derived
morphism by separate finite reductions. -/
theorem diagonalCoefficient_completedPullback (l : ℕ) [Fact l.Prime]
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (_hpl : p ≠ l)
    (Y Y' : Scheme.{u}) [Y.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
    [IsSeparated (Y' ↘ Spec (.of k))]
    [IsNoetherian Y] [IsNoetherian (ProjectiveLine Y)] [IsNoetherian (diagonalSurface Y)]
    [IsNoetherian Y'] [IsNoetherian (ProjectiveLine Y')] [IsNoetherian (diagonalSurface Y')]
    (g : Y' ⟶ Y) [g.IsOver (Spec (.of k))]
    [LocallyOfFiniteType g] [QuasiCompact g] [IsSeparated g]
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    [DiagonalTraceLocalizations l Y]
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l Y']
    [DiagonalTraceLocalizations l (ProjectiveLine Y')]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (_hcompletion : DiagonalCompletionSpec l (diagonalSurface Y) D)
    (_hsystem : DiagonalCycleSystemSpec l Y hY D)
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (_hcompletion' : DiagonalCompletionSpec l (diagonalSurface Y') D')
    (_hsystem' : DiagonalCycleSystemSpec l Y' hY' D')
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (_hδ : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (_hδ' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    (geometry : BaseSquares g)
    (family : Family l Y) (family' : Family l Y')
    (_reference : Reference l Y δ family) (_reference' : Reference l Y' δ' family') :
    Nonempty (PullbackCompatibility (Profinite.continuousMapRingObj.{u} ℤ_[l]) g
      (zlLine l) family.zl family'.zl
      (spIntegralComparison (baseP g) l (bottomField l))
      (spIntegralComparison (baseW g) l (bottomField l))) := by
  obtain ⟨data, hclass⟩ := diagonalCompletedClass_pullback l Y Y' g geometry hY hY'
    D D' δ δ' _hδ _hδ' _reference.eP _reference.eW _reference'.eP _reference'.eW
    _reference.sourceIso _reference'.sourceIso
    _reference.source_normalization _reference'.source_normalization
  rw [_reference.delta, _reference'.delta] at hclass
  refine ⟨{ sourceData := data, delta := hclass, traceq := ?_, trace₁ := ?_, trace₂ := ?_ }⟩
  · exact tracePullback_of_realized l
      (ProjectiveLine Y ↘ Y) (ProjectiveLine Y' ↘ Y') (baseP g) g
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g) hY hY'
      _reference.eP _reference.eY _reference'.eP _reference'.eY
      _reference.tq _reference'.tq family.zl.Rq family'.zl.Rq
      family.zl.q_canonical family'.zl.q_canonical family.zl.q_unit family'.zl.q_unit
      _reference.q_square _reference'.q_square data.endpoints.lineP data.endpoints.cY
      _ _ _reference.q_trace _reference'.q_trace
  · have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
      simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
    have hP' : IsUnit (l : Γ(ProjectiveLine Y', ⊤)) := by
      simpa only [map_natCast] using hY'.map (ProjectiveLine Y' ↘ Y').appTop.hom
    exact tracePullback_of_realized l
      (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.fst (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) (firstProjection_isPullback g) hP hP'
      _reference.eW _reference.eP _reference'.eW _reference'.eP
      _reference.t₁ _reference'.t₁ family.zl.R₁ family'.zl.R₁
      family.zl.p₁_canonical family'.zl.p₁_canonical family.zl.p₁_unit family'.zl.p₁_unit
      _reference.p₁_square _reference'.p₁_square data.endpoints.lineW data.endpoints.cP
      _ _ _reference.p₁_trace _reference'.p₁_trace
  · have hP : IsUnit (l : Γ(ProjectiveLine Y, ⊤)) := by
      simpa only [map_natCast] using hY.map (ProjectiveLine Y ↘ Y).appTop.hom
    have hP' : IsUnit (l : Γ(ProjectiveLine Y', ⊤)) := by
      simpa only [map_natCast] using hY'.map (ProjectiveLine Y' ↘ Y').appTop.hom
    exact tracePullback_of_realized l
      (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
      (pullback.snd (ProjectiveLine Y' ↘ Y') (ProjectiveLine Y' ↘ Y'))
      (baseW g) (baseP g) (secondProjection_isPullback g) hP hP'
      _reference.eW _reference.eP _reference'.eW _reference'.eP
      _reference.t₂ _reference'.t₂ family.zl.R₂ family'.zl.R₂
      family.zl.p₂_canonical family'.zl.p₂_canonical family.zl.p₂_unit family'.zl.p₂_unit
      _reference.p₂_square _reference'.p₂_square data.endpoints.lineW data.endpoints.cP
      _ _ _reference.p₂_trace _reference'.p₂_trace


end AlgebraicGeometry.ProEtale.DiagonalCoefficients
