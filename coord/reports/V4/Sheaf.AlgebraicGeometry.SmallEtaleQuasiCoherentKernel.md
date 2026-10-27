## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_smallEtale_kernel` in
`Sheaf.AlgebraicGeometry.SmallEtaleQuasiCoherentKernel`, with its statement and public imports
unchanged. Restrict the morphism to Zariski quasi-coherent modules, take the quasi-coherent
Zariski kernel, and show that extension preserves this kernel using the natural tensor-section
comparison already provided by the Zariski–étale equivalence. Étale pullbacks preserve kernels
by the existing proved flat-pullback exactness theorem; global sections preserve kernels.
Pointwise short-complex isomorphisms transfer exactness and monicity, and reflection of limits
identifies the extended kernel. Counit naturality then transfers the result to the original
morphism. Evaluation of its actual kernel proves the injectivity and exactness clauses.

Added two fully proved private helpers: additivity of restriction and the limit witness for an
extended kernel fork. The latter is a noncomputable definition because `IsLimit` is data, with
all its data explicitly constructed and no postponed proof. Added proof imports for flat
pullback exactness, additive adjunctions, short complexes, jointly reflecting evaluations, and
sheafification on étale slices. Only the item module, its own DAG node, and this report change;
there are no shared interface changes or consumer adaptations. Updated the node proof,
proof dependencies, proof origin, and the obsolete top-level tool approval.

The proof handles arbitrary schemes and morphisms, including the empty scheme, the zero
morphism, and the identity morphism: no nonemptiness, affine, finite-presentation, or
surjectivity assumptions are introduced. The proof with final import cleanup compiled on the project server in 16.9 seconds;
the delivery checks also validate the final documentation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_smallEtale_kernel`
(node `lem-trf-scheme-etale-quasi-coherent-kernel`). Proved 1 of 1 original holes;
0 holes remain in the item, 0 holes added, and 0 statements split off.
This is a proof from existing declarations, including the already-stated
`scheme_zariski_etale_quasiCoherent_equivalence`; it does not claim that all transitive
proof dependencies are already free of `sorry`.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.ZariskiEtaleTensorSections`: the equivalence theorem already
  supplies section comparisons and their compatibility with morphisms.
- `WeilConjectures.AlgebraicGeometry.StalkFlatTensorPullbackKernels`: the proved
  `flat_module_pullback_exact_pushforward_injective` directly supplies finite-limit
  preservation for the actual tensor pullback.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale` and
  `Mathlib.AlgebraicGeometry.Morphisms.Flat`: available through the retained and new imports.

Removed `lem-trf-zariski-etale-tensor-sections` and
`lem-sc-stalk-flat-tensor-pullback-kernels` from this item's proof dependencies and proof-step
uses. Removed the latter from the top-level `tool_uses` list while preserving the order of
all remaining approvals. Replaced the stalkwise argument by the existing proved node
`lem-weil-pbc-flat-module-pullback-exact-pushforward-injective`.
These are prunings of this item's proof route; no module is withdrawn, and no claim is made
that other consumers of these nodes have disappeared. All other declared dependencies are
used. The unit's mathematical route remains the Zariski kernel and étale flat pullback route.

## Where the brief, the DAG or earlier work was wrong

The original mathematical argument is sound. Its separate tensor-sections dependency is
unnecessary because the equivalence declaration already contains the needed naturality.
Its stalkwise-flat kernel step has a shorter, already proved implementation for the specified
scheme tensor pullback. Transport of quasi-coherence also needs sheafification on slice sites;
this is proved locally from the equivalence between the étale slice over U and the small
étale site of U. No definition, public statement, target, or unit route is changed.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
