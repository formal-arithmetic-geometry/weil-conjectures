# pbcScalarCompletedPullIso

## Reason

The completed coherence proof timed out at the 60-second file limit. The old
comparison encodes its two actual component maps through seven identity/associator
isomorphisms. Expanding that presentation repeats conversion of the chosen completion
functors. Use NatIso.ofComponents with exactly the same two component maps and prove
naturality directly. Keep the definition irreducible and expose a proved component lemma.

## Old

```lean
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  isoWhiskerLeft _ (Iso.refl (pbcActualCompletedPull g (pbcIntegralDatum l F))) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (pbcScalarOrdinaryPullIso l E F i g) _ ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ (pbcScalarCompletionIso l E F i X) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (Iso.refl (pbcActualCompletedPull g (pbcIntegralDatum l E))).symm _
```

## New

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Completed scalar/pullback is the ordinary comparison followed by the canonical
completion comparisons. Source: blueprint order 1307
(blueprint: prop-weil-pbc-scalar-extension). -/
@[irreducible] def pbcScalarCompletedPullIso :
    pbcEmbeddingAmbientTensor l E F i Y ⋙
        pbcActualCompletedPull g (pbcIntegralDatum l F) ≅
      pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
        pbcEmbeddingAmbientTensor l E F i X :=
  NatIso.ofComponents
    (F := pbcEmbeddingAmbientTensor l E F i Y ⋙
      pbcActualCompletedPull g (pbcIntegralDatum l F))
    (G := pbcActualCompletedPull g (pbcIntegralDatum l E) ⋙
      pbcEmbeddingAmbientTensor l E F i X) (fun K ↦
    (pbcActualCompletion (pbcIntegralDatum l F) X).mapIso
        ((pbcScalarOrdinaryPullIso l E F i g).app K) ≪≫
      (pbcScalarCompletionIso l E F i X).app
        ((pbcActualDerivedPull g (pbcIntegralDatum l E)).obj K)) (fun {K L} f ↦ by
    have he := (pbcScalarOrdinaryPullIso l E F i g).hom.naturality f
    have hc := (pbcScalarCompletionIso l E F i X).hom.naturality
      ((pbcActualDerivedPull g (pbcIntegralDatum l E)).map f)
    dsimp only [CategoryTheory.Functor.comp_map] at he hc
    dsimp only [pbcActualCompletedPull, CategoryTheory.Functor.comp_map, Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, Iso.app_hom]
    rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, he,
      CategoryTheory.Functor.map_comp, Category.assoc, hc, Category.assoc])

```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcScalarExtension | A2 | Proved component API and coherence proofs. |
| Sheaf.Paper.ContinuousRationalDerivedRealization | unclaimed | Uses the hom component to define its comparison. Identical component map. |
| Sheaf.Paper.OrdinaryAdjunctionScalarCompatibility | unclaimed | Composes the inverse component with strict pull comparisons. Identical component isomorphism. |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | unclaimed | Uses the inverse component in its normalization equation. Identical inverse. |
| Sheaf.Paper.RationalPurityPresentation (quarantined) | unclaimed | Uses the inverse component under tensor and shift functors. Identical component isomorphism. |

The first four rows are the direct declaration users reported by
`tools/downstream.py Sheaf.Paper.PbcScalarExtension --uses pbcScalarCompletedPullIso`;
the final row additionally checks the quarantined source. None of these consumers unfolds
this irreducible definition. No consumer requires adaptation. The public signature and
canonical hom and inverse components are identical. This is a construction normalization;
no hypothesis, conclusion or mathematical notion changes. Targets depending on this
comparison require the usual definition-change review under stage 2 §4.

## Status

landed 20261021T060925-L-1667352 2026-10-21 (merge of deliver/A2/Sheaf.Paper.PbcScalarExtension)
