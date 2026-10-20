/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Geometric reducedness and scheme-theoretic dominance

Geometric reducedness over a field descends along a quasi-compact scheme-theoretically
dominant morphism. This isolates the public helper formerly in
`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre` from the radicial construction.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Geometric reducedness over a field descends along a quasi-compact
scheme-theoretically dominant morphism.

Source: Stacks Project, Morphisms, Tags 081I and 056B
(`lemma-flat-base-change-scheme-theoretic-image` and
`lemma-scheme-theoretic-image-reduced`).
Proof: for any map Spec K to Spec k, its pullback to X is flat. Base change h
along this flat map. It remains quasi-compact and scheme-theoretically dominant.
Pullback pasting identifies its source with the base change of W to Spec K,
which is reduced by the geometric reducedness hypothesis. Injectivity on all
section rings then implies that the base change of X is reduced. This holds
for every field K and every base map, which is geometric reducedness of X.
The argument includes empty schemes and imposes no finiteness or affineness
hypotheses on W or X.

(blueprint: lem-sbc-geometrically-reduced-dominant-descent) -/
theorem geometricallyReduced_of_schemeTheoreticallyDominant
    {k : Type u} [Field k] {W X : Scheme.{u}}
    (h : W ⟶ X) (p : X ⟶ Spec (.of k))
    [IsSchemeTheoreticallyDominant h] [QuasiCompact h]
    (hred : GeometricallyReduced (h ≫ p)) : GeometricallyReduced p := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro K _ y
  let a := pullback.fst p y
  have : Flat a := inferInstance
  have : IsReduced (pullback h a) := by
    let e := pullbackRightPullbackFstIso p y h
    have : IsReduced (pullback (h ≫ p) y) :=
      hred.geometrically_isReduced _ _ _ (.of_hasPullback _ _)
    exact isReduced_of_isOpenImmersion e.hom
  exact IsSchemeTheoreticallyDominant.isReduced (pullback.snd h a)

end AlgebraicGeometry
