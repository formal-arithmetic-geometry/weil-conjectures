## What changed

Replaced the body of `WeilConjectures.directImageCoefficientExchange_isIso` without
changing its signature, visibility, or original public import. The proof uses the
already proved ordinary finite-free scalar mate theorem
`PurCompactSupport.properComparison_isIso_of_finiteFree` and
`finiteFreeCompletedScalarComparison`. The name `properComparison` does not impose
properness: its finite-free invertibility theorem applies to every scheme morphism.

Added `DirectImageLimitComparison` and `DirectImageScalarRealizationSquare`, each
with one named lower obligation. The first supplies normalized direct-image/limit
data on the entire quotient sequence site. Its two additional definitions are
explicit constructions: the derived ordinary-presentation isomorphism and the
reconstruction natural transformation. The second states equality of the specified
ordinary and system scalar mates in the reconstruction square.

The assigned proof establishes invertibility of reconstruction at the two inputs,
of the two scalar-completion maps, and of the ordinary scalar mate. It applies the
square and cancels its invertible prefixes. The scalarized input is obtained from
the existing intrinsic constructible scalar-extension functor. A private proved
helper converts intrinsic completeness to the unrestricted predicate through the
existing legacy comparison with an auxiliary prime larger than l.

## Proved and sorry left

This is a decomposition, not a complete proof of the transitive obligation.

Closed the assigned module's one hole:
`WeilConjectures.directImageCoefficientExchange_isIso`.
The assigned module has zero remaining holes.

All three modules compiled together with `lcompile.py --all`. Profiling showed
short declaration checks; the printed set timings also include staging. The
profiling options were removed. The fixed statement retains `fs`, `fft`, `fqc`,
which this route does not need; its unused-section-variable lint is suppressed
only for that theorem, preserving every original hypothesis. The two competing
completed-module category instances are disabled only within individual
declarations during elaboration, with no exported instance change.

Added exactly two holes, each in a new module:

- `WeilConjectures.directImageLimitComparison`, node
  `lem-weil-direct-image-limit-comparison`.
- `WeilConjectures.directImageScalarRealizationSquare`, node
  `lem-weil-direct-image-scalar-realization-square`.

The first is a one-coefficient general direct-image/limit compositor, with no
scalar extension or exchange invertibility conclusion. The second is a map
normalization equation, with no invertibility conclusion. Together with existing
finite-free and constructibility results they yield the assigned theorem by the
complete categorical proof in the item. Neither is the original IsIso proposition
under a different name. No data is chosen from either existence theorem inside a
definition: the limit comparison is an explicit parameter to reconstruction and
the square; the proof eliminates its Nonempty wrapper.

## No longer needed

No original Lean import was removed and no module is withdrawn or claimed globally
pruned. No unused proof-dependency imports were added.

`lem-fix-basic-operation-coefficient-coherence` /
`Sheaf.Paper.BasicOperationCoefficientCoherence` is no longer a direct dependency
of this proof: its ordinary scalar invertibility clause is supplied by the already
proved `lem-pur-finite-free-proper-scalar-comparison` /
`Sheaf.Paper.FiniteFreeProperScalarComparison`.

The original direct uses of `lem-coef-semilinear-derived-sections`,
`lem-trf-integral-pullback-comparison-realization`, and
`lem-weil-strict-roos-comparison` have been localized to the new map-normalization
obligation. They remain needed there; this delivery does not globally prune them.
The original `lem-sf-integral-direct-image-constructible` is still used through
`FrobeniusExchange.directImage_constructible` in the existing realization module.
Its separate module is not directly imported here because that declaration already
provides the required intrinsic constructibility.

## Where the brief, the DAG or earlier work was wrong

No statement correction. The unit's realized statement and proof-step nodes are
unchanged. The original plan's warning against proving invertibility on arbitrary
systems is respected. The quotient scalar maps need not be flat.

The ordinary finite-free direct-image part already exists as a proved theorem;
it is unnecessary to import the larger, still-holed basic-operation coherence
conjunction for that part. Existing `StrictMixedSystemModels` includes normalized
limit comparisons only with properness and absolute-separatedness hypotheses,
which the assigned theorem does not have. Its LimitComparison data structure is
reused verbatim, while the general compositor is isolated as a new theorem.

The general ringed-topos composition theorem is used as a generic tool by the new
limit-comparison proof plan. The source is Stacks `sites-cohomology.tex`,
lemma-derived-pushforward-composition (0D6E), lemma-derived-limit-is-ok (0941),
and lemma-Rf-commutes-with-Rlim (0A07). The actual blueprint direct-image and
final compatibility paragraphs were read in the latest checkout. Identity maps,
zero complexes, and empty schemes obey the displayed section and Roos formulas;
no argument infers equality from finite derived evaluations alone.

## New nodes

`lem-weil-direct-image-limit-comparison` records the single-coefficient normalized
ordinary and derived direct-image/limit comparison. Its source proof is the
common-ringed-pushforward argument, retaining the ordinary projections and the
whole-complex derived-unit equation. It reuses existing `LimitComparison` data
rather than defining a replacement notion.

`lem-weil-direct-image-scalar-realization-square` records the actual scalar mate
square after reconstruction. It isolates the second step of the assigned node's
original proof: expand the specified reduction counits and scalar mate, use the
tensor-generator equality and both signed Roos coordinates, then the normalized
derived units. The remaining Lean proof performs the finite-free argument and
cancellation instead of merely applying a renamed invertibility obligation.

Both nodes were searched with LeanSearch, LeanFinder and Mathlib grep. The exact
queries and results are in their `mathlib_searches` fields. Project and blueprint
searches found the related proper-case strict mixed models and the generic
constant-ring tower theorem, but neither supplies the required general
varying-quotient-ring normalized square. The overlaid dependency graph was checked
for missing citations, proof-dependency/uses equality and cycles involving the three delivered nodes.
No existing module besides the assigned item is changed; no change record or
forced adaptation is required.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
