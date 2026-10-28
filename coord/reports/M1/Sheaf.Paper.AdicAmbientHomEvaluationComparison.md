## What changed

Proved `adic_ambient_hom_evaluation_comparison_core_adjunction` without changing its
statement or moving any public declaration. The proof computes the Hom bijection as
postcomposition with the actual evaluation transpose, constructs its inverse using the
existing boundedness theorem and the realization image criterion, and proves pair
naturality and evaluation by uncurrying. All new helpers are private and proved.

The transpose calculation reuses the earlier N4 delivery's categorical proof; the Hom
bijection, inverse construction, two-variable evaluation calculation, and completion of
all five conclusions are supplied here. No dependency on that unlanded delivery remains.

## Proved and sorry left

Closed one of the three original holes:
`WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_core_adjunction`
(node `lem-sf-adic-ambient-hom-evaluation-comparison-core-adjunction`).

Two unchanged holes remain in this module:

- `WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_core_bounded`
  (node `lem-sf-adic-ambient-hom-evaluation-comparison-core-bounded`).
- `WeilConjectures.AdicQbarRealization.AmbientHomEvaluation.adic_ambient_hom_evaluation_comparison_coherence`
  (node `lem-sf-adic-ambient-hom-evaluation-comparison-coherence`).

No holes were added or split off. The completed adjunction theorem still depends on
the boundedness theorem and the existing normalized common evaluation naturality theorem.

## No longer needed

Removed five unused proof imports:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative`
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`
- `Sheaf.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale`

No DAG module is withdrawn. The finite-realization cocone and the separate ringed derived
adjunction existence theorem are not needed by the completed adjunction proof: its
realization, source transpose and ambient closed adjunction are already hypotheses.
They may still be needed to prove the unchanged boundedness and coherence obligations.

## Where the brief, the DAG or earlier work was wrong

The core-adjunction node's old proof dependencies omitted its use of ambient Hom
boundedness. The inverse construction requires that result before applying the
realization's image criterion. The updated node explicitly records this dependency
and the normalized common evaluation naturality theorem used for pair naturality.
The proof tests only realized H and a realized representative of Q; it does not assume
that constructible objects detect isomorphisms among all ambient objects.

The recorded global build error is an inherited bad import of NativeAdicRealizationData;
that dependency and the item both compile with the current published artifacts.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicAmbientHomEvaluationComparison": "c8e6083b91f0414a8e616904ddfd71dc8e78a50c"}, "results": {"Sheaf.Paper.AdicQbarConstructibleRealization": {"hash": "7e2ce2076ec6ff2ae7f31dd670b20fca6d09af3f", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T09:50:51+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
