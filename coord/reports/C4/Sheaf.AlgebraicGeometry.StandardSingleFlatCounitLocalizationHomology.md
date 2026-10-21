## What changed

Restored `lean/Sheaf/AlgebraicGeometry/StandardSingleFlatCounitLocalizationHomology.lean`
from the exact quarantine archive named by its `coord/rework.tsv` row. Changed the
proof import of `Sheaf.AlgebraicGeometry.OpenFlatComplexStalkCounit` to `import all`.
This exposes the comparison implementation needed during elaboration and kernel
checking. Removed the redundant proof import
`Sheaf.Paper.DerivedHomMayerVietoris`.

The original archive fails at line 132 while unpacking the scalar-extension pair:
`Tactic generalize failed: result is not type correct`. A diagnostic variant using
a named pair instead reaches the kernel error
`unknown constant ModuleCat.extendScalars_additive_sheaf`. The full counit import
fixes both failures with the original proof. A separate public import of the
scalar-extension instance provider was tested and proved unnecessary; it is not
in the delivery. Every byte after `@[expose] public section` equals the archive,
including the theorem statement, private helper, full proof, docstring, universes
and attributes. The public import is unchanged. No definition, target or adopted
source-library module is changed.

Validation: the final item compiles without errors or warnings through
`lcompile.py` in 23.7 seconds. A separate scratch set compiles the item with
axiom probes in 22.3 seconds and its unchanged archived direct consumer,
`StandardSingleFlatCounitLocalizationCompletion`, in 7.3 seconds. The main
statement, private flatness helper and consumer all depend on exactly `propext`,
`Classical.choice` and `Quot.sound`. The import-direction check permits the
counit dependency. All Lean lines are at most 100 characters.

The live downstream query finds zero importers because the module and its parent
are quarantined. The combined live/archive import graph has one direct consumer
and 93 transitive consumers; all are inventoried with current holders in the
change record. No adaptation is needed. The archived parent is tested only in
`scratch/consumer/` and is not delivered. Existing quarantine sources remain intact.

The existing node `lem-pc-standard-single-flat-counit-localization-homology`
already records exactly this proof: construct the specified stalk complex;
transfer its bound and flatness; obtain the universal scalar-extension pair;
combine the open-arrow and local counit comparisons with the presentation
isomorphisms. All four recorded proof dependencies remain used. Its Lean
attachment and the unit route are preserved; there is no mathematical route or
statement change requiring a node update. The relevant Stacks arguments were
read in `perfect.tex`, `lemma-single-complex-base-change` (0DJ9), and
`cohomology.tex`, `lemma-check-K-flat-stalks` (06YB) and
`lemma-derived-pullback-composition` (0D5S).

Searches: LeanFinder returned flat stalk-map and open-restriction infrastructure,
without a shorter matching comparison. Loogle found `Module.Flat.trans`, already
used by the private flatness helper. The logged Mathlib grep found no matching
scalar-extension additivity declaration in its queried directory. Repository
searches found the complete existing comparison and localization-pair proofs.

Change record:
`coord/changes/C4-standard-single-flat-counit-localization-homology-imports.md`.
Only the restored item, that record, and this report are delivered. Diagnostic
files and the consumer check live under the sandbox's `scratch/` directory.

## Proved and sorry left

This rework item has zero original holes and zero remaining holes.
`AlgebraicGeometry.standardSingleFlatCounit_localization_homology`, node
`lem-pc-standard-single-flat-counit-localization-homology`, retains its complete
proof. The private `AlgebraicGeometry.flat_restrict_iso` is also fully proved.
Holes closed: none (0 of 0). Holes added: none. Split off: none. Every `sorry`
left in the delivered Lean: none. This is a restoration and import repair,
not a newly closed theorem hole or a decomposition.

## No longer needed

Removed only the redundant direct proof import
`Sheaf.Paper.DerivedHomMayerVietoris`, a retired re-export of
`WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris`. The retained
`FlatSheafStalk` import already supplies that upstream dependency. No whole
module, mathematical dependency node, unit statement, unit step or proof
obligation is pruned. In particular all four recorded proof dependencies
(flat stalks, the localization pair, the open stalk arrow and the local flat
complex counit) remain needed. Every retained proof import supplies a theorem
actually used by the proof or its flatness helper. No quarantine archive is
withdrawn or altered.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a module with holes, but the assigned module
is a quarantined zero-hole rework item. Its absence from `lean/` is not a
withdrawal. Restoring the archive alone fails against the current published
interfaces; the full local counit import is necessary. The earlier B4 consumer
check recorded success after adding a public instance-provider import. In the
present environment that import alone still fails at the pair destructuring;
the full counit import resolves the failure and makes the extra provider
unnecessary. The DAG statement and proof route remain correct. No new result
or statement correction is introduced.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
