## What changed

The public signatures and definition bodies are unchanged. Private helpers construct
unsigned ordinary evaluation by the proved chain-level right-tensor currying equivalence,
establish its coefficient formula and uniqueness, and compare its localization through
the fixed augmentation maps and tensor coherence. The node records this shorter route.
The local proof context is documented in
`coord/changes/C9-ringed-ordinary-evaluation-proof-context.md`; it changes no public interface.

The localization proof resolves the arbitrary source complex, applies the fixed curry
normalizations to its dual and to the total tensor, identifies the resulting maps using
associator and unit coherence, and cancels the isomorphism induced by the resolution.
The two augmentation hypotheses supply precisely the two claimed comparison isomorphisms.
Local opacity keeps the complex-category and quasi-isomorphism definitions from unfolding
during instance matching.
The delivery gate compiles the complete module and checks its declarations.

## Proved and sorry left

The sole original hole, `CategoryTheory.ringedOrdinaryEvaluation_localization`, now has
a complete proof body. The packet removes 1 original sorry and introduces 0 sorries.
No sorry remains in the item, and no theorem is split off. The proof uses the existing
named dependencies; it changes none of their statements or definitions.

## No longer needed

Removed the direct private import
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`: the supplied
`CoefficientTensorModels` and `RingedDerivedTensorCoherence` contain the representative
comparisons used here. Its DAG statement dependency is retained because the statement
still refers to the canonical tensor model. No module is withdrawn.

The explicit differential construction in the original plan is unnecessary: the proved
chain-level tensor-Hom equivalence supplies the chain map and its unsigned generator
formula. The direct signed-comparison proof dependency is replaced by
`lem-sf-ringed-derived-tensor-hom-adjunction`, which already proves that equivalence.
The signed comparison remains a transitive dependency of that module and is not pruned.
No separate proof that the coefficient unit is K-flat is needed; the supplied one-K-flat
comparison handles tensoring with it.

## Where the brief, the DAG or earlier work was wrong

No statement correction is proposed. The existing chain-level unsigned currying API
shortens the original ordinary differential calculation. `RingedSiteDualityMaps` would
be circular at the DAG level and is not imported.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
