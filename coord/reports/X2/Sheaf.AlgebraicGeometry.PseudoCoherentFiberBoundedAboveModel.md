## What changed

Restored `lean/Sheaf/AlgebraicGeometry/PseudoCoherentFiberBoundedAboveModel.lean`
from its quarantine archive, as assigned by its row in `coord/rework.tsv`.
The archive was removed from the live library after the cluster restore; it was
not withdrawn mathematically. The restored module retains its original complete
proof, public imports, theorem signature, and private helpers verbatim. No other
module is delivered. This restores the declaration required by
`lem-sc-pseudo-coherent-fiber-finite-free-model` and its quarantined parent module.

The proof unpacks pseudo-coherence, shrinks to an affine neighbourhood, and
restricts the finite-free sheaf complex while preserving its upper bound.
The private helpers explicitly construct finite free coordinate modules and
lift their conjugated differentials by full faithfulness of affine
sheafification. Faithfulness proves square-zero and reflects vanishing above
the bound. The derived restriction comparison then supplies the model required
by `affine_boundedAbove_fiberBetti_eq`, which is applied to every degree and point.
Ranks and isomorphisms are chosen from the pseudo-coherence hypothesis; the
complex data are constructed rather than chosen from an unproved existence.

Validation: compiled the restored item through `lcompile.py` in 20.0 seconds,
without errors or warnings. A temporary, unchanged copy of the current source
of `AffineBoundedAboveFiberBettiComparison` was compiled first in the sandbox
overlay because the published compiled dependency still imported the retired
Sheaf copy of `DerivedFiberBetti`, causing a duplicate declaration error. That
temporary source copy was removed; it is not part of the delivery. The delivery
tool additionally runs the declaration axiom probe and project preflight.

## Proved and sorry left

This is a zero-hole restoration: 0 original holes, 0 holes closed, 0 holes added,
0 split off, and 0 remaining in the delivered module.
`AlgebraicGeometry.Scheme.exists_pseudoCoherent_fiber_boundedAbove_model`
(node `lem-sc-pseudo-coherent-fiber-bounded-above-model`) has a complete proof.
The private theorems `affine_free_iso` and `affine_local_finiteFree_model` also
have complete proofs. No new theorem or dependency hole is introduced. An explicit `#print axioms`
check of the public theorem returned exactly `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`; that check compiled in 38.4 seconds.
The temporary print command was removed before delivery.

## No longer needed

None. No import, module, node, or declaration is pruned or withdrawn. All four
current proof dependencies remain used: the pseudo-coherence definition, the
affine tilde/Gamma Mathlib leaf, the supplied affine fibre-Betti comparison,
and the derived-fibre Betti definition. The existing node's proof already
matches the restored Lean proof, so no DAG fields need changing. The unit
`sk-prop-av-cube` and its route are preserved.

Searches found no shorter exact replacement: LeanFinder returned support and
representative results without finite-free terms or fibre comparison; Loogle
found the `SheafOfModules.mapFreeIso` API used in the proof; msearch grep found
no affine lift result. Direct repository search found the spectrum-only
`affine_finiteFree_sheaf_complex_lift` and the existing private localized-site
construction in `PerfectOfPseudoCoherentFiniteTorDimension`. The latter already
underlies this complete localized-site proof; replacing it by the spectrum-only
lemma would require additional transport and does not shorten the argument.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an unfinished obligation, but the current rework
assignment is restoration of a quarantined theorem whose proof already contains
zero holes. The supplied-model fibre comparison has also since been proved and
restored; it is neither restated nor split off again here. Restoring the missing
module is the actual repair, rather than a proof no-op on an existing live file.

Read the current node and its dependency signatures, its parent node, the unit
record, and the affine reduction in `literature/stacks-project/perfect.tex`,
`lemma-jump-loci` (Tag 0BDI). The proof preserves the statement for all degrees,
with no lower bound on the representative. Empty opens have no points; the
existence conclusion chooses an open containing the supplied point. Rank-zero
terms, negative upper bounds, and the zero complex are covered by the explicit
Finsupp construction and faithful reflection of zero objects. No definition,
target statement, or source-library declaration is changed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
