## What changed

Proved `AlgebraicGeometry.isFlasque_homObj_of_coherent_injective` in
`Sheaf.AlgebraicGeometry.IsFlasqueHomObjOfInjective`, preserving its signature and all
public imports. Added proved private helpers constructing the canonical extension-presheaf
map to the source module, proving its monicity sectionwise, and performing injective lifting
through its sheafification. A local Hom section extends to a global morphism, then restricts
to the requested larger open. The existing extension-by-zero component formula verifies
that this construction lifts the original section.

Updated the item's DAG proof, dependencies and proof origin to this argument. No other
module, public declaration, statement or definition changed. New helpers use actual
constructions and complete proofs. Empty index sets, empty opens and identity inclusions
are covered by the same argument. The coherence and Noetherian hypotheses remain in the
statement; the proof does not need them.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.isFlasque_homObj_of_coherent_injective`
(node `lem-sc-ext-coherent-hom-injective-flasque`). Added 0 holes; 0 split off.
No `sorry` remains in the delivered Lean module, including its private helpers.

## No longer needed

Removed proof imports `WeilConjectures.Algebra.Homology.ModuleStalkExact` and
`WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction`.
The nodes `lem-weil-pbc-module-stalk-exact` and
`lem-weil-pbc-module-extension-by-zero-adjunction` are not used by this proof, and their
obsolete tool-use entries are removed from the item's node. The smaller proved node
`lem-weil-pbc-module-extension-by-zero-hom-formula` suffices for the adjunction and its
component formula. Monicity follows directly from the subsingleton indexing of extensions
by zero, followed by Mathlib's left exact sheafification; no stalk criterion or stalk
properties are needed. These modules and nodes remain in the library for other consumers.
All original public imports remain necessary for the unchanged statement or its API.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect found. The DAG's argument through the map between
two extensions by zero is longer than necessary: taking the larger open to be the whole
space extends each Hom section globally, and all other restriction surjections follow.
The unit's realized statement and steps remain untouched. Large scheme definitions and
inferred direct-sum index instances initially slowed elaboration; generic private helpers
and explicit component types avoid this without changing any library definition or the
single-file compile limit.

Change record: `coord/changes/a9-hom-injective-flasque-proof-commands.md` records
the new namespace opens and declaration-scoped elaboration options flagged by preflight.
The direct and transitive consumers retain the same theorem interface.

## Second reading by A9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
