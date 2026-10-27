# AlgebraicGeometry.ProEtale.QuotientSectionTensor.section_pull_transport_condition_of_normalized

## Reason

The original intermediate lemma omitted normalization of its endpoint derived isomorphisms.
`SectionPullNormalized` mentions the ordinary comparisons and the model counits, but does
not mention `cX.derived` or `cY.derived`. Its conclusion does mention both. For identity
coefficient and scheme maps with integral coefficients on a nonempty scheme, replacing one
normalized derived isomorphism by its negative preserves the hypotheses and changes the
conclusion from an identity comparison to its negative. The comparison of the source is
fixed by the endpoint computation equations. Both endpoint normalizations were already
hypotheses of the final transport theorem. No target, definition, or unit statement changes.

## Old

```lean
theorem section_pull_transport_condition_of_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T)
    (hnorm : SectionPullNormalized a f cX cY barLam) :
    PullSectionCondition a f cX cY lam barLam
```

## New

```lean
theorem section_pull_transport_condition_of_normalized {X Y : Scheme.{u}} (f : X ⟶ Y)
    (cX : ScalarSectionData a X) (cY : ScalarSectionData a Y)
    (hcX : ScalarSectionNormalized a X cX) (hcY : ScalarSectionNormalized a Y cY)
    (lam : D a Y ⋙ L Λ' f ≅ L Λ f ⋙ D a X) (hlam : PullNormalized a f lam)
    (barLam : cY.model.T ⋙ derivedPullback Λ' f ≅ derivedPullback Λ f ⋙ cX.model.T)
    (hnorm : SectionPullNormalized a f cX cY barLam) :
    PullSectionCondition a f cX cY lam barLam
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.QuotientSectionPullTransport | H1 | The sole caller, section_pull_transport, supplies its existing hcX and hcY hypotheses. Its signature is unchanged. |
| Sheaf.Paper.QuotientSectionTensorNormalization | unclaimed | Sole direct importer; does not call the corrected intermediate lemma. Check unchanged against the repaired module. |

The only DAG citer is lem-sfb-quotient-section-pull-transport. Its statement already
requires both endpoint normalizations and remains valid. The unit route is retained.

## Status

landed 20261027T233957-L-4149584 2026-10-27 (merge of deliver/H1/Sheaf.Paper.QuotientSectionPullTransport)
