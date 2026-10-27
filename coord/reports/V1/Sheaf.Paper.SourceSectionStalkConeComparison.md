## What changed

Reduced `WeilConjectures.trfSourceSectionStalkConeComparison` to two genuine steps of
its recorded argument: the identity completion-unit model, and the automorphism
restriction/insertion comparison. The original theorem has a complete assembly
proof. The restriction-model theorem obtains its section isomorphism from the existing
unbounded point-automorphism inverse theorem and its restriction formula, then
constructs its derived isomorphism using exact-functor coherence in the point
fibre's specified small-Hom localization dictionaries. The proof chooses
its compositor system and normalized quotient-germ/reparametrization families from
the existing dependency theorems, preserving all their specified maps.

The proof explicitly cancels the inverse unit and compositor using the coherent
source-unit equation: `trfSourceSectionC` is identity. Naturality of the given
derived inverse-image comparison and restriction proves derived naturality for
arbitrary arrows. Chain naturality follows from the strict lift equation,
naturality of the identity lift and tower reparametrization, and Roos functoriality.
The representative clause combines the distinct identity and source equations.

The five original definitions and structures are extracted verbatim to
`Sheaf.Paper.SourceSectionStalkConeData`, publicly reexported by the original
module, to permit the two independent proof modules without import cycles.
Signatures, bodies, universes, and all normalization clauses are preserved.
The new restriction module keeps the normalized section isomorphism behind a
private irreducible construction with a proved component API, avoiding repeated
reduction of its scalar-restriction and sheafification dictionaries.
Change record: `coord/changes/V1-source-section-data-extraction.md`.
There are zero current Lean consumers of the original module; the DAG use is
preserved, and no module is withdrawn.

Validation: the final sandbox `lcompile.py --all` run compiled all five modules
in import order, with no errors or warnings. All temporary profiling and diagnostic
code was removed before that check.

## Proved and sorry left

Original holes closed: `WeilConjectures.trfSourceSectionStalkConeComparison`
(node `lem-trf-source-section-stalk-cone-comparison`), 1 of 1.

New holes added, 2:

- `WeilConjectures.trfSourceSectionIdentityModel`
  (`lem-trf-source-section-identity-model`): the actual identity completion unit,
  both strict coordinates, and its equation for every representative.
- `WeilConjectures.trfSourceSectionAutomorphismModel`
  (`lem-trf-source-section-automorphism-model`): finite restriction-insertion,
  the strict entire-cone comparison, and its derived source representative.

This is a decomposition, not an end-to-end proof or net hole reduction: one
upper hole is closed and two lower holes are added. No holes remain in the item
module, data module, or proved restriction-model module. No definition contains a
hole, and no arbitrary witness from a holed existence theorem defines new data.

## No longer needed

No mathematical node or module is pruned. All original arguments remain needed
in the two smaller steps. In the item, the public imports of
`TraceStalkCompositorTowerRealization`, `GermReparametrizationDerivedDescent`,
`PointAutomorphismRestrictionNatural`, and
`IsomorphismDerivedPullbackComparisonNormalization` are reexported through the
new data module. The original private imports `CompletionUnitStrictQuotientModel`,
`QuotientTensorInsertion`, `IsoSectionwiseInverseImage`, and
`ProEtalePullbackStalkCoherence` are replaced by the precise proof modules; the
underlying dependencies remain imported where their proof steps need them.
No unused source-library declaration is removed or replaced with a hole.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement is changed or disputed. The prior seven-step plan
needs substantial glue between its completion/system presentations and the
quotient-stalk presentations. The two new holes isolate these actual steps;
neither restates the original existence-and-normalization theorem. The identity
step has no automorphism or source comparison. It explicitly assumes the already
available reconstruction coherence of I to supply compatible presentations. The automorphism step starts from
a given normalized identity lift and proves its separate source equation; it
does not construct that lift or prove the identity completion-unit equation.
Both retain arbitrary representatives, all integer degrees, and both cone
coordinates, rather than asserting detection of derived maps by finite reductions.

The new statements were checked conceptually for alpha equal to identity, zero
complexes and objects, exponent one, negative degrees, and non-cocycles. The
identity lift is defined on all complexes, and the strict automorphism equality
also quantifies all complexes. Its localization equation is restricted only to
the existing good representatives of constructible objects.

The proof additionally uses the existing
`lem-weil-point-automorphism-derived-transport-inverse` as a tool for the normalized
section and derived restriction isomorphisms, and
`lem-weil-isomorphism-comparison-natural` for derived naturality. These reuse
proved general interfaces, without changing the unit route.

## New nodes

`def-trf-source-section-stalk-cone-data` attaches the five verbatim extracted
constructions; it adds no theorem or mathematical assumption.

`lem-trf-source-section-restriction-model` is proved from the existing restriction
and inverse interfaces, specializing completed coefficients and their ordinary
derived factorization dictionaries.

`lem-trf-source-section-identity-model` is source-section step 2, including the
actual completion unit and the identity representative for every q.

`lem-trf-source-section-automorphism-model` is source-section steps 3--6: the
finite pointed-germ calculation, entire strict equality and derived source
representative. The parent performs the combination and both naturality proofs.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
