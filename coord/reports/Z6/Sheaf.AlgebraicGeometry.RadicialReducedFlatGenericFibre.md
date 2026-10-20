## What changed

Retired `Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`, which is marked
`retire` in the queue and already has zero holes. Its main declaration,
`AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre`, is present with the
identical statement and a complete proof in
`WeilConjectures.AlgebraicGeometry.RadicialReducedFlatGenericFibre`. Repointed
`lem-sbc-radicial-reduced-flat-generic-fibre` to that upstream declaration. No
upstream file changes, and no unit step or proof dependency of that theorem changes.

Preserved the item's other public result,
`AlgebraicGeometry.geometricallyReduced_of_schemeTheoreticallyDominant`, with
identical signature, visibility, and complete proof in the new focused module
`Sheaf.AlgebraicGeometry.GeometricallyReducedDominantDescent`. Its only import is
the Mathlib geometric reducedness module. Added a node documenting this existing
Mathlib-only argument, rather than introducing an unfinished result.

Changed the sole direct importer's private proof import:
`Sheaf.AlgebraicGeometry.FiniteInseparableGeometricReduction` now imports the
focused helper module. All its declarations, proofs, public imports, and attributes
are unchanged. Its node explicitly names the helper at the final descent step.
It is unclaimed; this is a one-line import adaptation.

The two delivered modules compile cleanly on the server (2.3 s and 4.2 s).
The upstream theorem also compiles, and `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

Change record: `coord/changes/retire-radicial-reduced-flat-generic-fibre-z6.md`.

## Proved and sorry left

Actual hole count before: 0. Holes closed: 0. Holes added: 0. Split off: 0.
No `sorry` remains in any delivered Lean file. This is a duplicate retirement,
not a claimed proof gain or a decomposition.

The canonical `AlgebraicGeometry.exists_radicial_reduced_flat_generic_fibre`
remains proved upstream with exactly its original statement. The relocated
`AlgebraicGeometry.geometricallyReduced_of_schemeTheoreticallyDominant` and
the adapted consumer's
`AlgebraicGeometry.exists_finite_purelyInseparable_geometricallyReduced_reduction`
retain their complete proofs.

## No longer needed

Withdrawn module:
`Sheaf.AlgebraicGeometry.RadicialReducedFlatGenericFibre`.
Its duplicate main theorem and its private
`geometricallyReduced_spec_of_isSeparablyGenerated` helper are no longer needed
in the Sheaf tree. The upstream theorem and its helpers are preserved verbatim.
`FiniteInseparableGeometricReduction` drops its private import of the withdrawn
module and imports only the public descent helper it actually uses.

The retired module's imports are removed with it:

- `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`
- `Mathlib.AlgebraicGeometry.Geometrically.Reduced`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`
- `WeilConjectures.AlgebraicGeometry.RadicialSeparatingGenericField`
- `WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced`

The focused module needs only the Mathlib geometric reducedness import.
The radicial separating-field and separably-generated tensor-reducedness nodes
are still needed by the canonical upstream theorem; they are not pruned from
the project. The radicial node itself is retained and repointed upstream.
The consumer's final step now cites the moved helper instead of directly citing
`lemma-nagata-dense-flat-pullback` and `def-pc-reduced-scheme`; reducedness is
still needed in its other steps. No general flat-base-change node is declared
globally unnecessary, and no source-library declaration or import is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open proof chain, but the current assigned
queue row is a zero-hole retirement. The entire chain is already proved upstream:
its radicial theorem's axiom audit is clean. Repeating that construction or
splitting it again would add no proof progress.

An earlier retirement pass kept this module because a consumer was pending.
That consumer is now unclaimed and its only use is the public descent helper,
which has no equivalent public declaration in the upstream twin. The helper
therefore must be preserved separately before withdrawal. The previous change
record `finite-inseparable-geometric-reduction-proof-context.md` explains why
the helper is public; this delivery preserves that interface and its proof.

`tools/downstream.py --uses` and a source import scan find one direct importer
and no external user of the radicial theorem through the retired module.
Neither the target statements nor their definitions change, and the same unit
route remains realized by the canonical upstream theorem.

## New nodes

`lem-sbc-geometrically-reduced-dominant-descent` records the existing public
helper at its new module. This fully proved result descends geometric reducedness
along a quasi-compact scheme-theoretically dominant map over a field, using flat
base change of schematic dominance, pullback pasting, and injective maps on
section rings. Its proof includes empty schemes and uses no affine or finite-type
assumption. Three recorded Mathlib searches and a blueprint search found no
separate public scheme-level result to reuse. No new proof obligation is created.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
