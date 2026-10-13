## What changed

Repaired the earlier attempt in `Sheaf.Paper.CechRefinementResolutionDiagram`.
The existing theorem signature and docstring stay unchanged. Constructed the total-homology
map explicitly as the forgetting-scalars image of the inverse source alpha, followed by
raw sections map r and target alpha. The existing `moduleCechAlpha_isIso` supplies the
inverse. Mathlib's `Functor.map_hom_inv_assoc` proves the alpha square without unfolding
the concrete total-complex definitions.

Added one proof import, `Sheaf.Paper.CechRefinementResolutionBeta`. Its named theorem states
only augmentation compatibility for this explicit map. Updated the parent DAG proof to
follow the actual construction and cancellation. Both modules compile individually within
60 seconds; the main module compiles in about 20 seconds.

## Proved and sorry left

Closed the direct hole in
`AlgebraicGeometry.Scheme.Modules.exists_cechRefinement_resolution_diagram` (1 of 1).
The existence witness and alpha square have complete Lean proofs. The beta square uses
`AlgebraicGeometry.Scheme.Modules.cechRefinement_resolution_canonical_beta`, the sole added
hole, node `lem-sc-cech-refinement-resolution-canonical-beta`.

This is a decomposition, not a completed proof free of sorry dependencies: one hole closed,
one added, net zero. Unlike the parent, the remaining statement has no existential witness
and asserts only the augmentation equation. The source alpha isomorphism and its
functorial cancellation are applied in the main module, not assumed in a new theorem.
The alpha cancellation is Mathlib's proved `Functor.map_hom_inv_assoc`.

## No longer needed

Removed the earlier sandbox's `Sheaf.Paper.CechRefinementResolutionAlpha` module and its
proof import. The earlier `exists_cechRefinement_resolution_beta` and
`cechRefinement_resolution_alpha` declarations and proposed nodes
`lem-sc-cech-refinement-resolution-beta` and `lem-sc-cech-refinement-resolution-alpha`
are not delivered and are not used. They were never part of the repository baseline.

No baseline import is removed. The original public imports are needed by the statement.
The parent no longer directly uses
`lem-weil-pbc-module-pushforward-injectives-sections-quasi-iso` or
`lem-sc-first-quadrant-total-column-comparison`; these remain needed in the new augmentation
lemma's proof plan, so no claim is made that their modules leave the target closure.
The old proof dependencies `def-sc-cech-refinement-cochain-map` and
`def-weil-pbc-module-cohomology-fmap` are also no longer direct parent proof dependencies;
they remain statement dependencies and proof dependencies of the augmentation lemma.
No established DAG module is globally pruned by this delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt still left the parent sorry, despite its report claiming a combination,
and its helper modules had no corresponding sandbox DAG records or source/proof docstrings.
More seriously, its alpha lemma claimed that any map satisfying the beta square satisfies
the alpha square. Beta is not assumed epi and generally is not: higher sheaf cohomology
need not come from Cech cohomology for the chosen cover. Thus a map can be changed on
classes outside the beta image without changing that equation. The source alpha
isomorphism determines the map from the alpha equation instead. The repair uses exactly
that direction and never assumes beta invertibility or a target cover.

Read the complete resolution diagram proof at https://stacks.math.columbia.edu/tag/01FD;
the local literature source and blueprint source directories are absent on this machine.
The available DAG unit record has empty realized slots; no unit statement or step changes.
Checked existing library signatures and performed LeanFinder, Loogle, and grep searches;
no existing declaration gives the remaining augmentation equation. LeanSearch was also
queried and returned Internal Server Error, recorded as unavailable.

Edge cases: an empty target family has zero cochain/total complexes in every degree, so
both equations have zero target and the construction still applies. An empty source
family can cover only an empty scheme; the existing alpha-isomorphism theorem includes
this case. Degree zero, repeated refinement indices, infinite families, and zero modules
introduce no additional hypotheses. No new definition, arbitrary existence choice, axiom,
statement weakening, target edit, or consumer adaptation is introduced.

## New nodes

`lem-sc-cech-refinement-resolution-canonical-beta`, in
`dag/nodes/sec-abelian-varieties/lem-sc-cech-refinement-resolution-canonical-beta.json`,
states the augmentation equation for the explicit source-alpha-transport map in
`Sheaf.Paper.CechRefinementResolutionBeta`. Its docstring gives the resolution zigzag,
column comparison, augmentation pentagon, raw sections comparison, and identification
with the explicit map. Source: Stacks 01FD, proof of Lemma 20.15.1. Its hypotheses match
the parent and do not require the target family to cover. It is the only new node and
only remaining delivered sorry. No change record is needed: existing interfaces stay
identical and the added import is private to the proof.

## Second reading by K1

1. Compared every delivered module with the repository baseline using diff. The sole
existing declaration's signature and docstring are byte for byte unchanged; no definition,
public import, visibility, target or consumer changed. The beta module is new. Verdict: pass.
2. Compiled both modules locally in import order. The parent constructs its witness from
the uniquely determined inverse of source alpha, proves its alpha equation by categorical
cancellation, and uses the beta lemma for precisely the other conjunct. No arbitrary
existence witness supplies data. Exactly one named theorem has sorry, as listed above;
there are no forbidden declarations or holes inside definitions. Axiom probes allow only
the three standard axioms and sorryAx from the remaining open statements. Verdict: pass
as a decomposition, not a sorry-free proof.
3. Read ModuleCohomologyFMapData (especially compatible, sections and invertible), the
refinement tuple formula and the alpha/beta constructions, and the full resolution
diagram in [Stacks 01FD](https://stacks.math.columbia.edu/tag/01FD). The beta lemma
asserts only the augmentation equation for a fixed constructed map; the parent really
constructs the witness and proves the other square. Its word proof supplies the necessary
resolution-column quasi-isomorphism and both commuting shapes. The target need not cover:
its alpha is never inverted. An empty target family gives zero target, and an empty
source cover forces an empty scheme; degree zero, repeated indices, infinite families
and zero coefficients cause no extra assumption. Independent LeanFinder search for
Cech augmentation naturality under ringed-space pullback, Loogle search for homologyMap
naturality, and local searches of both library roots found no replacement. The proved
moduleCechLiftSquares is restricted to one scheme and one family; the downstream
cechRefinement_comparison_square uses this parent and cannot replace it. Verdict: pass.
4. The construction uses the shortest available alpha argument. Existing public imports
are required by signatures; the beta proof import is private. Every removed old direct
proof dependency is accounted for under No longer needed, with no claim of global
pruning. Read dag/units/sk-prop-av-cube.json: realized.statement and its step slot are
empty, and no unit step, statement or route is changed. Verdict: pass.
5. Compared both node records with the Lean declarations. The existing node changes only
proof, proof_deps and proof_origin. Its dependencies follow the actual alpha cancellation
and beta application. The new node has its verbatim Lean signature, source, word proof,
searches, creation metadata and blueprint provenance; proof_deps is the union of its
steps' uses. Verdict: pass.

Changes on second reading: replaced the duplicate private map_inv_comp_cancel with the
pinned Mathlib theorem Functor.map_hom_inv_assoc, updated the parent node's cancellation
step accordingly, and completed the report's list of removed direct proof dependencies.
The first search returned a name from a newer Mathlib; checking the pinned source found
the appropriate available theorem. No additional hole was closed or introduced.
