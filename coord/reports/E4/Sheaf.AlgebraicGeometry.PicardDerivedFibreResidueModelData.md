## What changed

Simplified the complete proof in
`Sheaf.AlgebraicGeometry.PicardDerivedFibreResidueModelData` by proving tensor
pullback invertibility once in the private `tensorPullback_invertible_local`
helper. It uses `Modules.nonempty_tensorPullbackAdjunction`, already proved and
exported by `TensorPullback`, and uniqueness of left adjoints. Apply that helper
to the source coefficient and both successive target coefficient pullbacks.
The unused sectionwise normalization in `exists_tensorPullbackAdjunction` is no
longer requested.

Removed the private imports
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` and
`Mathlib.AlgebraicGeometry.AffineScheme`. Updated the existing node's first proof
step and proof origin; its mathematical statement, dependency list and Lean
attachment remain intact. No new module or public declaration is added.

The current source already has N4's universe repair and compiles unchanged in
19.4 seconds. The revised module compiles cleanly in 11.4 seconds. A textual
check verifies the public theorem signature and every public import are
byte-identical to that current source, with no lines exceeding 100 characters.
The quarantine-aware user scan finds two direct and twenty transitive consumers;
no adaptation is needed. In a separate scratch compilation set the revised
module compiled in 13.8 seconds, the unchanged archived
`PicardDerivedFibreResidueBridgeCore` in 19.5 seconds, and the unchanged archived
`PicardDerivedFibreResidueBridge` in 53.4 seconds, all cleanly within the limit. The assigned restoration and its quarantine archive
are preserved.

Change record:
`coord/changes/E4-picard-residue-model-adjunction-pruning.md`.

## Proved and sorry left

Zero holes before, zero holes after, zero holes closed, zero holes added, zero
split off. This is a listed rework item with an already complete proof; no
additional hole closure or decomposition is claimed.

The public theorem
`AlgebraicGeometry.Scheme.picard_derived_fibre_residue_model_data`
(node `new-picard-derived-fibre-residue-model-data`) remains fully proved from the
existing proper-direct-image perfection theorem and the local model definition.
All four private helpers, including the new pullback invertibility helper, have
complete proofs. There are no holed declarations in the delivered module and
no other Lean module is delivered.

## No longer needed

Removed the direct proof imports
`WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction` and
`Mathlib.AlgebraicGeometry.AffineScheme`. The sectionwise canonical-adjunction
theorem `Modules.exists_tensorPullbackAdjunction` is unused by this proof; its
plain existence counterpart in `TensorPullback` suffices.

An import-closure scan confirms both removed imports remain reachable through
retained dependencies, so zero whole modules or nodes are pruned. No source
library declaration is removed. Both declared proof dependencies,
`def-pc-perfect-complex` and
`lem-pc-proper-flat-single-derived-direct-image-perfect`, are still used.
The common finite intersection and affine refinement retain the unit's route.

## Where the brief, the DAG or earlier work was wrong

The current rework row records an earlier global-build failure after cluster
restoration. N4's landed explicit-universe repair already resolves that failure
in the source supplied to this session, as the initial clean compile confirms.
This delivery preserves that repair and simplifies a real proof dependency; it
is not a rebase or a compilation-only packet. No new definition repair or
failure of the current source is claimed.

LeanFinder found generic affine-neighbourhood results but no finite-family
perfect-model theorem. Loogle confirmed `RingHom.ker_isPrime`; the search service's
invertibility grep had no hits. Local source searches found the two-object
`perfect_common_affine_models` and the existing
`nonempty_tensorPullbackAdjunction`, which is the shorter adjunction route used
here. The former does not replace the simultaneous finite-family construction.
Read both declared dependency nodes and their Lean declarations, the current
cube unit, and the local Stacks definitions of strictly perfect and perfect
complexes. The finite intersection handles `n = 0` by giving top; a general
intersection is refined to an affine open, with no separatedness assumption.
No statement is disputed and no new node is introduced.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
