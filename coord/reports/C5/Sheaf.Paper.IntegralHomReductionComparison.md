## What changed
Constructed the normalized tensor models and scalar comparison in `integralHomReductionTensorData_exists` from the existing scalar internal-Hom adjunction model. Added three proved interfaces: componentwise currying of chain maps, normalization through the fixed K-injective augmentation, and transport of scalar tensor comparisons to a prescribed ordinary and universal derived extension.

The existing `coefficientHomComponent` definition now uses the cached `homComplexπ` selector. This is definitionally the same projection, by proof irrelevance; all existing signatures and selected data are preserved. A private proved compatibility equation connects it to the signed degreewise tensor–Hom API. Six direct consumers compiled unchanged; `DerivedAutomorphismHomEvaluation` reached the same 60-second limit with the original repository interface and with this presentation. The five delivery modules passed individual compilation checks; the final item compiled in 53.9 seconds without warnings. The definition change and its downstream census are recorded in `coord/changes/c5-coefficient-hom-projection-presentation.md`.

## Proved and sorry left
Closed the original hole `WeilConjectures.integralHomReductionTensorData_exists` (one of one). No new holes. The three new theorems `coefficientCochainTensorCurry_exists`, `coefficientTensorCurry_normalize`, and `ScalarTensorTransport.fixedScalarTensorComparison_exists` have complete proofs. They use existing project declarations, including the already stated scalar internal-Hom models, as authorized by stage 3.

## No longer needed
No existing module or declaration is withdrawn. The revised proof route is recorded in the item node and uses the scalar internal-Hom models together with the three new proved interfaces. No original proof-dependency imports were present in the item.

## Where the brief, the DAG or earlier work was wrong
The existence proof needs interfaces relating literal Hom-complex evaluation to the fixed normalized tensor models; an abstract derived adjunction alone does not supply the displayed section formulas. The DAG did not separately record these interfaces. The scalar extension selected in the generic model must also be identified with the specified integral extension, and its universal derived comparison transported along the counit-compatible natural isomorphism.

## New nodes
`lem-sf-coefficient-cochain-tensor-curry`: closed degree-zero global sections of the signed Hom–tensor chain isomorphism give the unique curried chain map, with its literal evaluation formula.

`lem-sf-coefficient-tensor-curry-normalization`: augment the target, apply the recorded uncurrying normalization, identify the resulting chain map on tensor generators, and cancel the augmentation in the derived category.

`lem-sf-scalar-tensor-comparison-transport`: identify ordinary extensions and transport the tensor comparison by uniqueness of universal left-derived functors.

Change record: `coord/changes/c5-coefficient-hom-projection-presentation.md`.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
