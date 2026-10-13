## What changed

Proved `AlgebraicGeometry.exists_openExtension_derivedAdjunction` in
`Sheaf.AlgebraicGeometry.OpenExtensionDerivedAdjunction` without changing its signature.
Added the proof-only import `Sheaf.Algebra.Homology.DerivedOpenShriekAdjunction`.
The proof constructs the derived over-site equivalence and composes its inverse's
adjunction with `derived_open_shriek_adjunction`. The left adjoint is the composite
of the inverse derived equivalence and canonical derived extension by zero, rather
than an arbitrary witness chosen from an existence theorem.
Updated the item's DAG proof and dependencies to record this route. A declaration-local
linter option suppresses the existing unused existential binder `adj` in `∃ adj, True`.
The module compiles without warnings using lcompile.py.

## Proved and sorry left

Closed the one hole in `AlgebraicGeometry.exists_openExtension_derivedAdjunction`
(node `lem-pc-open-extension-derived-adjunction`). No holes remain in the item;
no holes were added or split off. The imported `derived_open_shriek_adjunction`
already has a complete proof. Its lower dependencies remain existing work.

## No longer needed

No existing imports were removed: the public import `DerivedTensorStructure` supplies
names and instances in the unchanged statement and remains part of its public interface.
The proof no longer directly needs
`lem-weil-pbc-module-restriction-open-immersion-colimits`
(`Mathlib.AlgebraicGeometry.Modules.Sheaf`, restriction/pushforward adjunction and
colimit preservation); that proof-dependency edge was removed. No claim is made that
this Mathlib module becomes globally unreachable.
`lem-sc-derived-open-restriction-adjunction-exact`
(`Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact`) is no longer a direct
proof dependency, but remains needed transitively through
`lem-sc-derived-open-shriek-derived-adjunction`, so it is not pruned globally.
No other nodes or modules from the original proof plan are bypassed.

## Where the brief, the DAG or earlier work was wrong

The plan described constructing the derived adjunction from the underived one, but
`AlgebraicGeometry.derived_open_shriek_adjunction` already does that construction.
The item needs only the transport across the over-site equivalence, which is elementary
composition of adjunctions. The unit record has no realized statement/step attached to
this node, and the same extension-by-zero route is retained.
LeanFinder found generic derived-adjunction/localization tools; Loogle confirmed
`CategoryTheory.Adjunction.comp`. Local source search found the existing proved
ringed-space theorem and the derived-equivalence construction.

## Second reading by U1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; the only code changes are the proof-only import, proof body, and a declaration-local linter option for the pre-existing unused existential binder.
2. Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The adjunction is obtained by composing the proved derived open-shriek adjunction with the derived equivalence adjunction.
3. Checked the node statement against the Lean theorem and searched the local library and available theorem search results. No duplicate declaration or split-off statement was added; the existing node remains the sole theorem node and no new holes were introduced.
4. Checked the shorter route: `derived_open_shriek_adjunction` already supplies the derived extension/restriction adjunction, so the proof only transports it through `Scheme.Modules.overEquiv`; this removes the unused restriction-colimit dependency while preserving the unit's extension-by-zero route.
5. Checked the DAG proof, proof dependencies, and unit metadata. The sandbox node records exactly the two dependencies used by the proof (`lem-sc-derived-open-shriek-derived-adjunction` and `def-pc-derived-category`); the unit's realized route is unchanged.

Changed during second reading: no mathematical statements or definitions; retained the worker's proof and metadata, and added this review record.
