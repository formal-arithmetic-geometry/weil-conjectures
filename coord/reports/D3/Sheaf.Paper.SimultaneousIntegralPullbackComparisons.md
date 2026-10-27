## What changed

Reduced `WeilConjectures.integralPullbackComparisonRealization_simultaneous` to four
independent results: ambient primitive data, geometric composition laws, the mixed
square with naturality, and scalar unit/tower laws. The main theorem assembles all
fields for the same system. It proves the ordinary mixed scheme-unit equation from
quotient mixed composition and geometric units, using a proved generic cancellation
lemma and equality transport. It also proves rationalization by functoriality.

The existing theorem signature and public import are unchanged. All new proof
imports are private. No existing definition or statement is changed.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.integralPullbackComparisonRealization_simultaneous`
(`lem-trf-integral-pullback-comparison-realization`) by a complete Lean assembly.

Four new theorem holes remain:

- `WeilConjectures.ambientComparisonSystem_exists`
  (`lem-trf-ambient-comparison-system-existence`).
- `WeilConjectures.normalizedIntegralGeometricCoherence`
  (`lem-trf-normalized-integral-geometric-coherence`).
- `WeilConjectures.normalizedIntegralMixedCoherence`
  (`lem-trf-normalized-integral-mixed-coherence`).
- `WeilConjectures.normalizedIntegralScalarCoherence`
  (`lem-trf-normalized-integral-scalar-coherence`).

This is a decomposition: one original hole closed, four lower holes added, zero
holes in the item module and no definition holes. The lower statements fix an
arbitrary normalized system and cover disjoint parts of the argument; none asserts
existence of a coherent system or restates the original simultaneous theorem.

## No longer needed

No module is withdrawn and no existing public import is removed. The proof does
not directly use `effectiveComparisonRealizationModels`, whose scheme indices
require ell invertible. The ambient existence result supplies the larger family
required by `IntegralComparisonSystem`; this does not make the effective-model
module globally unnecessary.

The main assembly no longer directly imports counit substitution: its word
transport argument belongs to the three new coherence nodes, whose proof
requirements retain `lem-trf-counit-realization-substitution` and
`lem-trf-quotient-system-mixed-coherence`. Rationalization remains needed.
No dependency is claimed globally pruned.

## Where the brief, the DAG or earlier work was wrong

The original first assembly step cannot supply an ambient family from
`EffectiveComparisonRealizationModels`: its scheme indices require ell invertible,
while the stored system models, completion and scalar effectivity are unrestricted.
The ambient node records that gap explicitly.

The scalar-model equations use `CompletedLineTensor.chi` and the finite-free ordinary
scalar model, whereas the public scalar units and associators use the universal
ordinary scalar model and `scalarCompletionIso`. Their comparison must use the
balanced tensor and derived-counit normalization. The scalar coherence node's proof
records this required argument; the cyclic downstream ordinary-model comparison
cannot be imported directly here.

Substantial word-coordinate, adjunction-cut and geometric pasting calculations were
written and checked in focused compiler probes. The full unabstracted draft repeatedly
exposed expensive derived-category instance conversions. The delivered decomposition
uses the independent mathematical geometric, mixed and scalar results, each with a
complete natural-language proof. Temporary diagnostic proofs are excluded.

The latest blueprint no longer contains `prop-trf-karoubi-independence`. The original
unit and node statement remain; sources refer to the recorded Stacks construction.

## New nodes

`lem-trf-ambient-comparison-system-existence` supplies ambient normalized primitive
models and effectivity only. Its existential is eliminated inside a theorem proof;
no definition selects arbitrary data.

`lem-trf-normalized-integral-geometric-coherence` states geometric naturality,
associativity and both units for a fixed normalized system. Its proof is counit word
transport followed by quotient compositor coherence.

`lem-trf-normalized-integral-mixed-coherence` states mixed naturality and the integral
mixed square for a fixed system and embedding. Its proof pastes primitive mixed and
compositor squares, then cancels their common word coordinate.

`lem-trf-normalized-integral-scalar-coherence` states scheme-unit, coefficient-unit
and coefficient-tower compatibility for a fixed system and embedding. Its proof uses
the ordinary scalar-model normalization and whole-system scalar coherence. Identity
embeddings, zero objects and empty schemes satisfy the same formulas. These statements
change no assumptions or conclusion of any existing declaration. No change record is
required.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
