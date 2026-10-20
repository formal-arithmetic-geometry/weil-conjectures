## What changed

Restored `lean/Sheaf/Paper/ModuleCupResolutionFMap.lean` from the quarantine path in
`coord/rework.tsv`. Promoted the defining `ModuleCohomologyFMap` import to public so
`cupResolution_class_fmap` can state its existing signature. The change record is
`coord/changes/module-cup-resolution-fmap-visibility.md`.

Proved `AlgebraicGeometry.Scheme.Modules.cupResolution_class_fmap` without changing its
statement or either existing public definition. The proof compares directly with the
resolution choices already selected in `moduleCohomologyFMap`. Identity lifts, augmented
homotopy, naturality of sections, and naturality of the resolution and forgetting-scalars
homology isomorphisms give equality on global homology. Evaluating this equality on the
source cycle proves the required class formula. Added only proved private helpers.

Validation: `lcompile.py --all` compiled the item without warnings in 30.3 seconds,
then both unchanged quarantined consumers, `ModuleCupPullbackAugmentedPairings` and
`ModuleCupPullbackResolutionMaps`, in 12.0 and 8.5 seconds respectively. Their sandbox
copies were removed after checking; no consumer edits are delivered. A source comparison
confirmed all three existing public signatures are unchanged.

Updated the node's proof and proof dependencies to match this route. No other library
module, target, unit route, or declaration signature changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.Modules.cupResolution_class_fmap`
(node `lem-sc-module-cup-resolution-fmap`).

Holes added: 0. Holes left in the delivered module: 0. Split off: 0.
This is a proof, not a decomposition.

## No longer needed

Removed the private import
`WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial` and the proof dependency
`lem-weil-pbc-module-cohomology-fmap-functorial`. Using the choices already selected in
the definition avoids independence and avoids constructing fresh injective replacements.
No source-library declaration or module is removed. The functoriality module remains
available to its other users. No module is withdrawn.

All remaining imports supply statements, definitions or proof infrastructure used by the
file. No other stated dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The item source is quarantined, not withdrawn. Its rework row records a real visibility
error: the public theorem referred to `moduleCohomologyFMap` through a private import.
Restoration preserves its Lean attachment, public definitions, and all parent obligations.

The previous proof plan unnecessarily constructed replacement choices with D.I and E.I.
Instead, canonical identity lifts compare those resolutions to the choices already used
by the definition. This removes the need for the functoriality/independence theorem.
The argument applies uniformly in degree zero, with zero coefficients, and on the empty
scheme, without tensor-pairing assumptions or additional hypotheses.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
