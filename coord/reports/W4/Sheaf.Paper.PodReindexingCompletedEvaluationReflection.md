## What changed

Filled six of the module's nine original theorem holes without changing any public
statement or definition. The completion-unit bijection now follows directly from
the recorded reduction/limit adjunction. Private proved helpers reproduce the
published normalized reconstruction argument without its unused geometric
invertibility parameter, then prove the required abstract adjunction bijection.
The tensor-model isomorphism identifies this bijection with precomposition by the
original `unit`, including its orientation.

Proved the projection-normalized equality of reindexing functors, naturality of
ordinary and completed currying, the evaluation extension and uniqueness laws,
transport of constructibility through the ambient comparison, reflector
injectivity, and the final existential assembly from the existing reindexing and
shift declarations. The node's proof route and dependencies now describe this
argument. No source-library file or consumer interface changed.

## Proved and sorry left

Closed six original holes, all in `WeilConjectures.PodCompletedReflection`:

- `reindex_eq`
- `precompose_bijective`
- `reflection_laws`
- `constructible_hom`
- `coherence_iff`
- `podReindexingCompletedEvaluationReflection`

Added zero holes and split off zero statements. Three original named theorem
holes remain, with their original statements, source citations and complete proof
plans:

- `WeilConjectures.PodCompletedReflection.reindexing_laws`
- `WeilConjectures.PodCompletedReflection.signed_shifts`
- `WeilConjectures.PodCompletedReflection.identity_composition`

The final assembly uses the first two of these original declarations. Its closure
therefore still contains postponed proofs; this delivery does not claim an
axiom-free proof of the project's targets. All added private helpers are proved.

## No longer needed

Removed these private proof imports:

- `Sheaf.Paper.AmbientCompletedTensorAdjunction`
- `Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`

The proof no longer directly needs the corresponding nodes
`lem-sf-ambient-completed-tensor-adjunction`,
`lem-sf-ringed-derived-tensor-hom-adjunction`, or
`lem-pur-integral-operations-preserve-constructible`. The ordinary closed structure
is already recorded by the coefficient calculus; constructibility uses
`T.constructible` and isomorphism closure instead of another operations theorem.
The reflector proof also no longer directly uses
`lem-weil-pbc-constant-completion-equivalence` or
`lem-weil-pbc-ringed-koszul-completion-reflector`; the recorded adjunction and
normalized DVR/Roos effectivity give the unit's universal property directly.
The two original public re-export imports are preserved for existing consumers;
the reflector remains a transitive dependency of isomorphism closure. No module
is withdrawn or claimed globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The ambient completed-tensor lemma has a different completion presentation from
the actual reduction/limit unit in this module; it is not an immediate Lean
application to the displayed `unit`. The shorter available interface argument
uses the actual adjunction, with normalized reconstruction. The published
`purNormalizedReconstruction` proof does not use its `IsUnit` hypothesis, so the
same proof is valid over the arbitrary schemes quantified by
`precompose_bijective`. This generalization is private and fully proved here;
no published statement was strengthened or weakened.

Validation: the edited module compiled through `lcompile.py` (55.6 seconds).
The 24 original public declarations retain their signatures and data bodies.
The revised proof dependency union is exact and has no cycle back to this node.

The remaining three coherence declarations are not direct projections of the
existence theorem in `PodReindexingCompletionUnitTensor`: they quantify over
arbitrary data satisfying the normalization laws. In particular that theorem
supplies signed shifts for its chosen family, whereas `signed_shifts` must
identify arbitrary normalized data with the chosen maps. The existing
representative-level uniqueness arguments are still required, and their original
holes were retained instead of moving them to equivalent new statements.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
