## What changed

Replaced the sorry in
`AlgebraicGeometry.exists_normalized_flat_telescope_comparison` by a complete
Lean proof combining model-map normalization and common tower refinement.
For an arbitrary map `s`, obtain stage-induced `a` and `b` with `a ≫ s = b` and
`a` a quasi-isomorphism. Localization and functoriality make the image of `a`
invertible. Precompose the desired square by it, apply the two stage-map
naturality squares, and cancel. The translated-unit equation is retained exactly.

Added `FlatTelescopeStageMap`, `NormalizedFlatTelescopeStageComparison`, and
`FlatTelescopeStageMapRefinement`. The first module holds the two existing
predicates verbatim and explicitly defines model maps using countable sum maps,
mapping-cone maps, translation, and transport by homotopy isomorphisms.
The parent publicly re-exports the predicates. Its proof imports the other two
modules privately. The existing theorem signature and docstring are unchanged.

All four Lean modules compile together, individually below 60 seconds. The new
statements were checked on zero towers, zero maps, identities, and empty schemes.
No object is defined by choosing a witness of a new existence theorem.
The unit route is unchanged; the parent node realizes no separate unit step.
The source-layout change is recorded in
`coord/changes/flat-telescope-presentation-extraction.md`.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.exists_normalized_flat_telescope_comparison`
(node `lem-sc-normalized-flat-telescope-comparison`). No sorry remains in its module.
This is a decomposition, not a fully discharged proof: 1 upper hole closed and
2 lower holes added, giving a net increase of 1 pending hole before pruning.

New holes, each exactly a named public theorem with `:= by sorry`:

- `AlgebraicGeometry.exists_normalized_flat_telescope_stage_comparison`
  (node `lem-sc-normalized-flat-telescope-stage-comparison`): joint normalized
  isomorphisms and naturality only for maps induced by bounded-flat towers.
- `AlgebraicGeometry.exists_flat_telescope_stage_map_refinement`
  (node `lem-sc-flat-telescope-stage-map-refinement`): a common source refinement
  of an arbitrary homotopy map by two stage-induced maps. It contains no
  derived pullback, tensorator, or comparison-family assertion.

Neither lower theorem asserts the full original result. Full naturality uses
both and the written localization/cancellation argument. The foundational
module has no sorry.

## No longer needed

No node or module is globally pruned. The parent no longer directly imports
`Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat`,
`Mathlib.Algebra.Homology.HomologicalComplexLimits`, or
`Mathlib.Algebra.Homology.HomotopyCategory.MappingCone`; those remain public
imports of the shared presentation module and remain necessary there.
The parent's old direct proof dependencies now belong to the stage-normalization
subclaim rather than being independently used by the parent proof:
`def-pc-kflat-complex`, `def-pc-module-pullback`,
`def-pc-scheme-derived-tensor-structure`, `def-sc-scheme-canonical-shift-unit-iso`,
`def-sc-scheme-canonical-tensor-shift`, and `lem-pc-kflat-closure`.
They remain transitive dependencies; none is globally pruned.
No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The original step 3 omitted the exact
refinement interface needed to deduce naturality on arbitrary homotopy maps
from naturality on tower maps. It is now a separate geometric statement with
its witnesses and equality spelled out. Generic right-fraction calculus by
itself does not produce stage-induced maps: the compatible bounded-flat
diagram construction and homotopy rectification are part of the new open lemma.

The normalized K-flat counit and canonical pullback-shift theorems downstream
of this item cannot be imported here: doing so would create an import cycle.
Tags 06YS and 06YJ supply flat resolution and derived-pullback computations;
they do not literally state normalization for an arbitrary supplied tensorator
or the explicit stage-map refinement. Those are marked as agent expansions of
the parent's existing proof plan. LeanSearch was unavailable (HTTP 500),
recorded as unavailable; LeanFinder/Loogle and source searches were performed.

## New nodes

`def-sc-flat-telescope-stage-map` records the existing telescope predicates in
the shared module and the new explicit transition and stage-map definitions.

`lem-sc-normalized-flat-telescope-stage-comparison` isolates the joint
supplied-tensorator model calculation and naturality on its concrete stage maps.
Its imports provide the existing K-flat closure theory without a cycle.

`lem-sc-flat-telescope-stage-map-refinement` isolates the common bounded-flat
tower refinement used to extend that naturality. Its dependencies include the
existing bounded flat replacements, flat truncation towers and telescope
comparison, and the right-fraction equality criterion.

Change record: `coord/changes/flat-telescope-presentation-extraction.md`.

## Second reading by J2

1. **Statements and unchanged interfaces.** I compared all delivered modules with the
repository versions. The parent theorem signature is byte-for-byte unchanged, and the
moved telescope predicates have identical bodies and types. The two new statements are
strict restrictions of the parent argument: one handles only explicit stage maps, and the
other supplies a common telescope source and factorization; neither states the parent
comparison for arbitrary maps.

2. **Proof and compilation.** The four modules compile with `lcompile.py --all` and no
compiler errors. The parent proof uses only the two new lemmas, functoriality, invertibility
of the quasi-isomorphism image, and cancellation. The only remaining `sorry`s are the two
named open lower theorems, each with a source and complete proof plan in its docstring.
Explicit `#print axioms` probes show only `propext`, `Classical.choice`,
`Quot.sound`, and `sorryAx` for the three theorems; the stage-map definition uses
only the three standard axioms. There are no new axiom declarations, unsafe
declarations, hollow definitions, or opaque implementations.

3. **New statements and source checks.** I read the source pages for Stacks Tags 06YS,
06YJ, and 04VC and checked the edge cases recorded by the worker (zero towers, zero maps,
identities, and empty schemes). The stage-map definition constructs sum and mapping-cone
maps explicitly. The refinement theorem is strictly smaller than the parent because it
asserts only a common source, stage-map witnesses, and a right-fraction equality. Searches
recorded in the nodes found no existing declaration of either statement.

4. **Pruning and imports.** The parent’s former direct imports needed only by the extracted
predicates are now reached through `FlatTelescopeStageMap`; proof-only imports of the parent
are private. The shared presentation module retains its public imports. No unit route is
bypassed and no unrelated node is removed.

5. **DAG agreement.** The item and both split nodes record the declarations, statements,
proof dependencies, source locations, searches, and blueprint ancestry corresponding to the
Lean files. The unit remains the same. No statement-change record is needed for the parent.

I changed only the report by adding this second reading, explicit axiom-probe results,
and the complete list of old direct proof dependencies no longer used by the parent. No Lean proof or declaration was
changed during review.
