/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A9
-/
module

public import Sheaf.Paper.DiagonalCoefficientReference
public import Sheaf.Paper.DiagonalCoefficientPullbackEndpoints

/-! # Geometric inverse image of a normalized completed projective-line trace

Source: the latest blueprint, diagonal coefficient changes, proof paragraph (3).
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

/-- The canonical realization of the shifted positive line is an isomorphism.
Source: the exact realization's single and shift comparisons
(blueprint: lem-diagonal-completed-trace-pullback).
Proof: each of the three factors in shiftedLine is the image of an isomorphism. -/
theorem completedRealization_shiftedLine_isIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    [DiagonalTraceLocalizations l X] (e : CompletedRealization l X) :
    IsIso (e.shiftedLine l X) := by
  unfold CompletedRealization.shiftedLine
  infer_instance

attribute [local instance] completedRealization_shiftedLine_isIso

/-- Pullback of one completed projective-line trace, expressed in its normalized
condensed realization. This is a trace-only assertion for a Cartesian square of
arbitrary projective-line models; no diagonal class or coefficient family occurs.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
the base-changed unit/Chern decomposition and passage to its trace.
(blueprint: lem-diagonal-completed-trace-pullback).

Proof: form the unit/Chern decomposition for the two projective-line models as a
single morphism of strict Kummer systems. On the Cartesian square, the unit is
natural and the section class pulls back to the positive section class. If the
chosen models differ by a projective-line automorphism, the hyperplane classes
differ by a class from the base; this changes only the first summand and is killed
by the trace projection. Thus the twisted splitting square commutes after its
canonical coefficient identifications. Apply the normalized inverse-image/derived-
limit comparison to the entire splitting. Cartesian coefficients identify its
endpoints, so this comparison and the splitting are invertible. Consequently the
derived direct-image mate is invertible on the shifted positive line. Invert the
commuting splitting square and project to its constant summand to get the trace
square. The construction equations in t and t' identify these as the completed
traces. Transport by the four completed realizations and the two normalized
push squares. Their full universal-unit equations hcanonical and hcanonical'
identify the transported direct-image mate with modelExchange, rather than an
arbitrarily rescaled comparison. The displayed inverse factors just solve each
CompletedTraceCompatibility equation for its condensed trace. This argument
applies to q and to either projective model of a product projection. -/
theorem diagonalCompletedTrace_pullback (l : ℕ) [Fact l.Prime]
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
    (c : UnitPullEndpoint (Profinite.continuousMapRingObj.{u} ℤ_[l]) hS) :
    let trace := inv (D.R.map (eX.shiftedLine l X)) ≫
      push.derived.iso.inv.app _ ≫ eS.F.mapDerivedCategory.map t.trace ≫ eS.singleUnit l S
    let trace' := inv (D'.R.map (eX'.shiftedLine l X')) ≫
      push'.derived.iso.inv.app _ ≫ eS'.F.mapDerivedCategory.map t'.trace ≫ eS'.singleUnit l S'
    TracePullback (Profinite.continuousMapRingObj.{u} ℤ_[l]) f f' hX hS square.w.symm
      D D' canonical canonical' line c trace trace' := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
