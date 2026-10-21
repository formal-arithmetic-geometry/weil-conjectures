## What changed

Proved `AlgebraicGeometry.ProEtale.torAmplitudeIn_of_constructible_of_uniform_local_model`
in `Sheaf.Paper.StratifiedTorIntervalDevissage`, retaining its exact signature.
The proof uses the existing finite scheme-theoretic open-closed refinement and
`pullback_finiteConstantLocalModel`, then strong induction on the reverse vertex index.
Private proved helpers compare tensor with degree-zero pullback, detect the same Tor
interval on an open-closed pair, transport local models across isomorphisms, and handle
empty schemes with the empty cover. Root pullback reflects zero by its inverse.

The DAG proof records this internal-module route. No definition or statement changes,
source-library edits, consumer adaptations, or new public statements are included.
The change record `coord/changes/stratified-tor-interval-proof.md` explains the private generic helper section and local instance
attribute required to keep kernel checking below the file limit.

## Proved and sorry left

Closed one existing hole:
`AlgebraicGeometry.ProEtale.torAmplitudeIn_of_constructible_of_uniform_local_model`
(node `lem-sfb-stratified-tor-interval-devissage`). Added zero holes. The item has zero
remaining holes; no intermediate result is split off. Dependencies retain their existing
proof status. The complete file compiled successfully in 35.1 seconds through
`lcompile.py`; final compilation and preflight are recorded by the delivery tool.

## No longer needed

Removed proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalLocalDetection`: the private helper proves
  the needed fixed-interval detection directly for internal modules, using the existing
  normalized derived tensor comparison and open-closed zero detection.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: the existing model-pullback lemma
  supplies the cover pullback and model identification.
- `Mathlib.CategoryTheory.Adjunction.CompositionIso`: use the existing `upperStarComp`.

The original public imports and the explicit Cartesian-coefficients unit-route import
are retained.

Direct proof dependencies no longer needed: `lem-sfb-tor-interval-local-detection`,
`def-weil-proetale-inverse-image`, and `sk-prop-sfb-cartesian-coefficients`. The last
node remains a transitive dependency of model pullback; its old direct `tool_uses`
entry is removed. `det-def-sfb-constructible-local-model` stays a statement dependency
and participates in the empty-leaf argument; its matrix criterion is unnecessary.
`new-proetale-derived-module-pullback-monoidal` is also unnecessary: the proved
`def-sfb-condensed-pullback-tensor-comparison` supplies the normalized comparison,
transported along `supportPullbackIsoUpperStar`.
No modules are withdrawn and no upstream declarations are removed.

## Where the brief, the DAG or earlier work was wrong

The planned site-level local-detection theorem uses sectionwise modules and its own
specified tensor, while the item uses internal modules and the monoidal derived tensor.
Using the already available internal-module tensor comparison and zero-detection theorem
avoids that additional comparison. The finite refinement and its actual leaf
factorizations are retained; no factorization is inferred from image containment.
The proof covers empty roots and leaves without assuming zero belongs to the interval.
The coefficient admissibility and ordered-interval hypotheses are preserved, although
this devissage argument itself works without them. No unit route changes.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
