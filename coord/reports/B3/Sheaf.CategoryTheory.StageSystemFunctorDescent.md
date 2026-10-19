## What changed

Proved `CategoryTheory.StageSystem.coefficientPairFunctor_exists` in
`Sheaf.CategoryTheory.StageSystemFunctorDescent`. Added the proof-only import
`WeilConjectures.CategoryTheory.StageSystem.Functor` and reused its existing
`StageSystem.Morphism.functor`. The coherence hypothesis is exactly the `coh`
field of a stage-system morphism. The object and representative formulas are
reflexive; uniqueness uses `Functor.hext` and `PairCategory.hom_induction`.
All existing signatures, definitions, universes, visibility and public imports
are unchanged. Updated the attached node's proof to describe this implementation.

## Proved and sorry left

Closed the sole hole, `CategoryTheory.StageSystem.coefficientPairFunctor_exists`
(node `lem-sbc-coherent-pair-functor-descent`). Holes closed: 1. Holes added: 0.
No sorry remains in the delivered module. No split-offs or new modules.
Current remote single-file compilation passed with no diagnostics in 2.0 seconds;
the import-direction check also passed.
The preexisting publicly reexported `CommonStage.coherent_pair_functor_descent`
is outside this item's module and is unchanged.

## No longer needed

Removed the unused proof-only import
`Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: the theorem is generic over
a directed preorder and uses no coefficient-field construction. The original
public imports are retained as the existing API, including the separately
specified additive and Karoubi interface. No module is claimed globally pruned,
since `CoherentPairFunctorDescent` still publicly imports the coefficient fields.

For this attached StageSystem theorem, the old fourteen-step reconstruction of
pair-category operations, additive structures, transformations and Karoubi
extension is unnecessary. Its former proof dependencies are not used by this
proof: `def-weil-preadditive-category`, `def-weil-pbc-additive-functor`,
`def-weil-finite-subextension-directed-set`,
`def-weil-directed-colimit-abelian-groups`, `def-weil-size-convention`,
`def-weil-additive-category`, and `def-weil-karoubi-envelope`. The indexing and
category hypotheses are already explicit in the unchanged theorem, and the
upstream functor constructs the quotient map directly. The node's proof_deps
are therefore empty. This does not withdraw the separately reexported
CommonStage declarations or claim those nodes globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The attached theorem's proof plan proposed reconstructing descent, although
`WeilConjectures.CategoryTheory.StageSystem.Functor` already provides the exact
construction on the actual quotient. Its coherence and formulas match without
normalization or additivity assumptions. The broad original node also describes
the separately retained CommonStage interface; this delivery proves the specific
StageSystem theorem currently attached to it. The unit `sk-rem-rest` has no
realized statement or proof steps to bypass. No mathematical statement repair
or forced adaptation was necessary.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
