## What changed

Restored the quarantined module `Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsDerivedModel`
from its preserved archive. The supplied K-flat terminal-section complex is reconstructed
as a complex of sheaves, its derived residue pullback is computed by the existing affine
K-flat comparison, and residue scalar transport identifies the result with the complex
in the original statement. The public statement and all three mathematical dependencies
are preserved.

Also simplified the private complex-comparison helper and the restriction comparison
in `Sheaf.AlgebraicGeometry.AffineKFlatResiduePullbackModel` after its unchanged source
exceeded the 60-second compile limit. Both comparisons use the induced natural
isomorphism directly; the identity composition isomorphisms are definitionally
unnecessary. The assigned theorem uses the same direct comparison. The dependency also uses
the direct left-adjoint additivity lemma instead of constructing finite-colimit
preservation to deduce additivity. No public
signature, import, visibility or instance changes. Details and the consumer inventory
are in `coord/changes/R1-affine-residue-complex-comparisons-restoration.md`.

## Proved and sorry left

The archived item had zero direct holes. The restored declaration is
`AlgebraicGeometry.Scheme.affineFree_residueSections_derivedModel`
(`lem-sc-affine-free-residue-sections-derived-model`). Zero holes closed, zero holes added,
zero holes left in the item. The adapted theorem
`AlgebraicGeometry.Scheme.affine_kFlat_residuePullback_model`
(`lem-sc-affine-kflat-residue-pullback-model`) also has zero holes before and after. No decomposition or new statement is introduced.

Validation: server compilation of both delivered modules passed. The complete
maintainer axiom probe for the final adapted dependency passed in 48.9 seconds
(`SHEAF-PROBED 2`, no disallowed axioms or holes); the restored item compiled in
29.6 seconds. A source comparison checks both public signatures byte-for-byte.
The sandbox Lean files contain no `sorry` and no added axiom. The archived direct
consumer `AffineFreeResidueSectionsCohomology` compiled unchanged against the compiled
sandbox modules in 18.8 seconds; its temporary source copy is excluded from delivery.

## No longer needed

None of the three declared proof dependencies is pruned. All are used by the proof.
The adopted `WeilConjectures` declarations of terminal-section reconstruction and residue
scalar transport are retained. No module or DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

This is a quarantine-restoration item, rather than an item with a textual `sorry`.
The absence of the live module does not permit withdrawing its declaration: the quarantined
`AffineFreeResidueSectionsCohomology` proof still applies it, and sixteen further archived
modules depend on that consumer. The source node and the unit route are retained.

The archived composition comparisons added expensive kernel checks despite having
definitionally equal endpoints. Applying `NatIso.mapHomologicalComplex` directly
proves the same comparisons with smaller terms. No mathematical route is changed.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
