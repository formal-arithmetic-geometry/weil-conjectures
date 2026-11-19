# PR1559 classification

Phase: the historical report attributes the before/after target cost to Kernel checks. Current porting is blocked by API drift, so the old source is not a valid successful current-master benchmark.

Exact component: `Functor.OplaxMonoidal.ofLaxSquare` and the application of `leftDerivedUpperStarTensorComparison` in `Comparison.lean`. The fix introduces `LaxSquareHδ` as a named `Prop`, `ofLaxSquareHδ`, and `app_app_comp_of_eq`; these prevent conversion under the commutative-square structure and expose argument-wise comparisons.

Label: **E (representation/interface mismatch), with A (reduction/definitional equality) contributing**. Confidence is medium to strong from the PR's controlled kernel timings and source-level change. The current before port's 9.05 GB failed run is retained only as a porting record.

