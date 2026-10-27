## What changed

Extracted the existing normalized data interface into
Sheaf.Paper.AdicPurityScalarNaturalityData and publicly re-exported it from the
assigned module to avoid cycles with the two new intermediate theorem modules.
The existing functors, normalizations and field propositions are retained. Coherence
is exposed so its eight conjuncts can be assembled in the importing theorem.
Local irreducibility is respected during data elaboration, with the original
settings retained locally in reductionBridge and sourceShift.
The original theorem now assembles normalizedComparisonConstruction and
canonicalSourceCoherence with a complete private cancellation argument.
The exceptional unit and associativity equations follow from the purity square,
source equations, naturality and cancellation of scalar images of gamma.
The exceptional scalar shift equation follows by expressing b as the composite
of whiskered gamma inverse, a and whiskered gamma. A proved generic helper
handles shift compatibility of this conjugate, with recorded instances explicit.

Validation: all four delivery modules and all four unchanged direct consumers
compile through lcompile.py --all. The theorem signature matches the original
verbatim. Temporary consumer copies were removed after verification.

Change record: coord/changes/R2-adic-purity-comparison-data-extraction.md.

## Proved and sorry left

Closed the original hole in
WeilConjectures.AdicPurityScalarNaturality.adicPurityScalarNaturality (one of one).
The private comparison_coherence proof transfers source coherence to exceptional
coherence and combines all eight required equations.

Added two strictly smaller holes, each the entire proof of a public named theorem
in its own module:

- WeilConjectures.AdicPurityScalarNaturality.canonicalSourceCoherence
  (lem-pur-adic-canonical-source-coherence): the canonical source comparison's
  tensor-unit, associativity and shift equations, without purity data.
- WeilConjectures.AdicPurityScalarNaturality.normalizedComparisonConstruction
  (lem-pur-adic-normalized-comparison-construction): construction of normalized
  natural transposes, their reductions, scalar square and purity shift equation;
  excludes all source and exceptional tensor-cocycle equations and the scalar
  comparison shift equations.

This is a decomposition, not a net hole closure: one original hole closed and two
added. The data module has zero holes. Its expensive operation-property record is
stored in three smaller inherited records. Its source properties use a generic
PropertyFamily proof wrapper to bound kernel checking; named projections expose
the original propositions.
No definition uses a new existence witness.

## No longer needed

No mathematical dependency or module is pruned. The five original proof dependencies
remain needed below the new source-coherence and normalized-construction statements.
The original public prerequisites moved verbatim to the publicly re-exported data
module. Its operation-property constructor now uses three inherited records;
no consumer uses the old positional constructor or eliminators. The two new theorem
imports are private. No source-library declaration,
import, quarantine path or old node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The five existing dependencies expose different presentations: ambient schemes
versus SixFunctorSpace, raw field subtypes versus shrunk coefficient carriers,
exact-derived ordinary scalar extension versus K-flat localization, and completed
trace coordinates versus ordinary tensor coordinates. None states the comparison
interface's entire normalized assembly directly. The new statements isolate those
remaining interface transports rather than pretending their normalizations are
judgmentally equal. Their proof plans retain the original trace route and never
infer equality of arbitrary maps from equality of their finite reductions.
The purity square already implies the exceptional tensor cocycles and scalar
shift equation once the source cocycles and gamma shifts are known; the explicit
Lean argument removes those equations from the remaining construction obligation.

Edge checks: identity field inclusions use the actual ordinary tensor unit;
three-field towers use its actual associator; d=0 gives no crossing sign;
empty schemes and zero complexes require no nonzero trace or orientation
uniqueness assumption. Every cancellation is by an isomorphism.

## New nodes

- def-pur-adic-purity-scalar-naturality-data owns the relocated existing data
  declarations and adds no mathematical assertion or hole.
- lem-pur-adic-canonical-source-coherence isolates the source tensor and shift
  equations from lem-pur-adic-operation-domains-source-comparison.
- lem-pur-adic-normalized-comparison-construction isolates the normalized
  trace/reduction interface assembly using all five original dependencies.

The unit and chapter route are preserved. The parent proof_deps now name the two
new steps; the original five dependencies remain their stated proof dependencies.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
