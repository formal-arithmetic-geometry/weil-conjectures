## What changed

Restored the quarantined `Sheaf.AlgebraicGeometry.SourceCocycleExactRestriction` from
its recorded archive. Its complete original cocycle theorem and three private proofs
are retained verbatim. Added one public import of the new module
`Sheaf.AlgebraicGeometry.StrictHenselizationSchemeSectionsExact`, whose proved instance
supplies finite-colimit preservation for global sections on the original
`Scheme.strictHenselizationScheme s`.

The proof uses the adopted source's `strictHenselizationLocalStructure` for the actual
coordinate-ring colimit and its generic strictly henselian terminal-sections theorem,
then transfers epimorphism preservation to Γ and applies Mathlib exactness results.
The cocycle node retains its Lean attachment and all old dependencies, and gains the
new exactness node in its first proof step. No source-library file is changed.

Compiled both delivered modules in import order without warnings: 3.1 seconds for the
new instance and 16.8 seconds for the restored item. Separate `#print axioms` checks for
both public declarations list exactly `propext`, `Classical.choice`, and `Quot.sound`.
An import smoke check synthesizes the original-model exactness instance.
Read the local Stacks source, Tag 03QO, lemma-vanishing-etale-cohomology-strictly-henselian,
and checked the existing unit record `sk-prop-h2`: its realized arrays are empty, and no
unit statement or proof route is changed.

Change record: `coord/changes/H4-source-cocycle-original-model-exactness.md`.

## Proved and sorry left

This is a zero-hole compilation repair, not a new proof of an existing hole.
The archived `AlgebraicGeometry.Etale.sourceCocycleExactRestriction` was already fully
proved; its missing exactness instance is now supplied for the scheme it actually uses.

New fully proved declaration:
`AlgebraicGeometry.Etale.strictHenselizationScheme_globalSections_preservesFiniteColimits`
(node `lem-weil-pbc-strict-henselization-scheme-sections-exact`).

Holes closed: 0 of 0. Holes added: 0. Split off with sorry: 0.
Sorries left in the item and the new module: none.
The original private helpers `exactHomologyProjection`, `sourceSectionsCocycleRestriction`
and `exactHomologyTransport` remain completely proved.

## No longer needed

None. No module, declaration, import or old dependency is withdrawn or pruned.
In particular the quarantined source, its Lean attachment, and all 74 downstream
quarantined modules are preserved. The source-library twin has a different strict-local
model and therefore does not directly replace the assigned statement.
All imports of the new module are used: two public imports supply its statement's
scheme, site and sections functor; three private imports supply the proof's additive
sections, local-ring structures, and exact terminal sections.

## Where the brief, the DAG or earlier work was wrong

The recorded compiler failure is real. Since the upstream sync,
`strictHenselization_globalSections_preservesFiniteColimits s` concerns
`Scheme.strictLocalization s`, whereas the archived cocycle statement still uses
`Scheme.strictHenselizationScheme s`. These are separate Lean constructions. Merely
reintroducing the old file, or applying the same-named source theorem, does not fix it.
The generic adopted source local-structure theorem already supplies precisely the
ring properties needed for a short direct repair; no new mathematical hole is needed.

The shared live tree has no current importers. A scan including quarantine confirms
one direct parent, `Sheaf.AlgebraicGeometry.StrictLocalLocalizedHomGerm`, and 74 total
downstream modules. A scratch compile of that unchanged direct parent still reports
its separate canonical/colimit-model mismatches, first at lines 57 and 95, and errors
in exposed definitions. These are pre-existing rework defects of that parent, not
forced adaptations caused by this interface-preserving repair. No other module is
included in this delivery. The original cocycle theorem's signature is unchanged,
including arbitrary τ, all integer degrees, and the zero-cocycle edge case.

## New nodes

`lem-weil-pbc-strict-henselization-scheme-sections-exact` records exactness for global
sections on the spectrum of the actual affine-neighbourhood colimit. Its source is
Stacks Tag 03QO. Its proof uses the existing local-structure declaration and terminal
section exactness; the new instance is fully proved and uses no sorry-dependent axiom.
LeanSearch, LeanFinder, Loogle and local source searches were run and recorded. This
node is an exactness prerequisite of the restored cocycle calculation, not a renamed
copy of the cocycle theorem or an unfinished split.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
