## What changed

Completed `AlgebraicGeometry.etaleInverseImageScalarDistributivity_left` by obtaining the abelian addition transport from `etaleInverseImageAbelianLift_operations`, proving the source sectionwise `smul_add` diagram, applying the new generic product-comparison transport theorem, and evaluating the resulting diagram on sections. Added the proof-only import and the new module `Sheaf.AlgebraicGeometry.ProductComparisonDistributivity`.

## Proved and sorry left

Closed `AlgebraicGeometry.etaleInverseImageScalarDistributivity_left`. Also proved `CategoryTheory.Limits.productComparison_distributivity`, recorded by node `lem-weil-pbc-product-comparison-distributivity`. Closed 1 of 1 original holes; 0 holes split off or added. No `sorry` remains in either delivered module. The target may still inherit axioms from existing dependencies, which are unchanged.

## No longer needed

The original route's proof dependencies `lem-weil-pbc-conjugate-iso-unit-equation` and `lem-weil-pbc-etale-inverse-image-algebraic-structures` are not needed as proof steps. The existing public import of `EtaleInverseImageAlgebraicStructures` remains because it exposes the statement's types. No public imports were removed. Ring addition transport and a separate comparison-uniqueness argument are unnecessary for module-variable additivity.

## Where the brief, the DAG or earlier work was wrong

The inherited attempt had the categorical transport proved but failed in the final section evaluation. Explicit equality conversions repair the mismatch between underlying-set and abelian-section types, and between composition evaluation and successive application. The existing abelian operation theorem handles the supplied comparison directly. The source diagram and section evaluation now compile without warnings.

## New nodes

`lem-weil-pbc-product-comparison-distributivity` records the proved generic binary-product transport lemma in `lean/Sheaf/AlgebraicGeometry/ProductComparisonDistributivity.lean`.

The new statement was checked for identity functors and identity isomorphisms (it reduces to its source diagram), arbitrary additions with no unit or associativity, and empty section sets. Only binary-product preservation is used. LeanFinder returned eight monoidal distributivity results, grep returned product-comparison projection results, Loogle did not recognize the unqualified identifier, and LeanSearch returned HTTP 500; the node records these actual outcomes. Blueprint search found no duplicate.

## Second reading by S2

1. I compared both delivered modules against the repository versions. Existing target and declaration signatures are unchanged; the added generic theorem is recorded as a new node.

2. I compiled `ProductComparisonDistributivity.lean` and `EtaleInverseImageScalarDistributivityLeft.lean` with the launcher. Both compile cleanly, with no `sorry`, forbidden declarations, or hollow definitions; the proof uses only ordinary category-theoretic constructions and inherited dependencies.

3. The split-off `CategoryTheory.Limits.productComparison_distributivity` is a genuine generic transport lemma, strictly more general than the target and needed by its proof. Its statement was checked on identity functors, arbitrary binary operations, and empty products; its node and docstring give the source and proof. No duplicate declaration was found.

4. The proof follows the unit route through abelian operation transport and product comparison. The proof-only imports are minimal for the delivered proof; the old conjugate-isomorphism and algebraic-structure proof dependencies are not used and are listed above.

5. The DAG proof, proof dependencies, origin, and new node agree with the Lean proof. The section evaluation uses explicit product projection identities and preserves the target statement exactly.

I repaired a definitional-equality issue in the final section evaluation by changing the introduced scalar to the local alias `R'` before constructing the categorical product section. No statement or definition was changed.
