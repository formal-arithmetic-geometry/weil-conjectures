## What changed

Prove `WeilConjectures.OrdinaryStratifiedModels.modelPullback_existsUnique`, the item's
remaining hole. Add a private proof import of `Sheaf.Paper.FiniteProjectiveModelPullback`
and reuse its proved comparison on all scalar modules. Extend the existing objectwise
comparison with the concrete tensor realization to a natural isomorphism. Its action on
pure tensor sections follows from naturality of sheafification. Transport the normalized
comparison through this isomorphism; naturality of the original ordinary pullback unit
preserves the displayed generator formula. The constant-model adjunction shows that terminal
constant generators determine a map; injectivity of the ordinary pullback adjunction Hom
equivalence then proves uniqueness.

All new helpers are private and proved. Move the existing private tensor-model helpers before
the theorem so they can be reused. Existing public statements, constructions, public imports
and target meanings are preserved. Update the item's DAG proof and dependency list to name
the reused normalized-model result. Local irreducibility controls keep the transported
comparison from unfolding during proof elaboration; they do not change the public interface.

Validation: the complete module compiled successfully on the server in 56.7 seconds with
profiling enabled. Profiling options are removed for delivery. All 25 existing public
declaration signatures were compared with the source and are unchanged.

Search: Lean Finder and Loogle return ordinary free-module pullback comparisons; repository
search locates the already proved `FiniteProjectivePullback.allComparison` and its generator
formula. The import-direction check permits the proof import.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.OrdinaryStratifiedModels.modelPullback_existsUnique`
(node `lem-tw-ordinary-pullback-stratified-models`).

No sorry remains in the item. No holes added or split off. This is a proof, not a decomposition.

## No longer needed

No imports removed and no modules or nodes newly pruned. Existing scalar-unit, flatness,
K-flatness and coefficient-coherence dependencies remain used by the established proofs.
The already pruned ordinary-immersion/chart-comparison dependency remains absent. The unit's
realization has no prescribed statement or proof steps that this route bypasses.

## Where the brief, the DAG or earlier work was wrong

The normalized comparison for arbitrary scalar modules is already proved as a private helper
in the finite-projective-model module. The remaining work here is the natural, generator-
preserving identification of the selected scalar realization with that concrete tensor
realization. No statement dispute or definition repair is needed. The source contains the
restored item and the completed finite-projective proof; historical rework records do not
justify withdrawing either module.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
