## What changed

Replaced the hole in `WeilConjectures.purSequenceKFlatComparisonShifts` by an assembly
of a normalized universal counit, explicit resolution comparisons, stability of K-flat
resolutions under shifts, the signed Mathlib tensor shift, and descended shift coherence.
The resolution comparisons are constructed by inverting the image of the resolution map;
their counit equations, naturality, finite evaluation and three-resolution coherence are
proved directly. K-flat shift stability uses the signed tensor shift and stability of
acyclic complexes under shifts.

Two new modules isolate the outstanding descent arguments:
`Sheaf.Paper.PurSequenceReductionUniversal` and `Sheaf.Paper.PurSequenceReductionShifts`.
These are proper parts of the original assertion, not renamed copies of it. The first
only supplies a universal counit on the already supplied reduction and its normalized
representatives. The second assumes a universal comparison and supplies its coherent shifts.
Neither asserts the resolution-comparison identities or the tensor statement proved here.

The six existing data declarations were relocated verbatim into
`Sheaf.Paper.PurSequenceKFlatComparisonData`, publicly re-exported by the original module,
to let the new lemmas refer to them without an import cycle. No existing signature,
field, definition body, visibility or target changes. See
`coord/changes/J8-pur-sequence-kflat-comparison-data.md` for consumers and old declarations.

Validation: all four delivery modules compile cleanly. The item compiled standalone in
47.1 seconds and in the consumer batch in 45.6 seconds. Unchanged consumers
`PurSequenceComparisonTranspose`, `PurSequenceDerivedNormalization`,
`PurSequenceProjectionHomNormalization`, and `BasicRealizationShiftSquare` all compile
against the relocated public declarations. The latter existing consumer took 86.6 seconds
in the batch; it is unmodified and is not part of the delivery.

## Proved and sorry left

Closed the original body hole of
`WeilConjectures.purSequenceKFlatComparisonShifts` (one original hole), conditionally
on the two smaller statements below. This is a decomposition, not a sorry-free proof
of the original mathematical assertion. Private helpers `resolutionComparison` and
`shiftKFlat` contain complete proofs.

Added two named theorem holes, each exactly `:= by sorry`:

- `WeilConjectures.purSequenceReductionUniversal`, node
  `lem-pur-sequence-reduction-universal`.
- `WeilConjectures.purSequenceReductionShifts`, node
  `lem-pur-sequence-reduction-shifts`.

There are no holes in definitions and no remaining holes in the item module. The packet
has two theorem holes in total: one original hole closed, two lower holes added (net minus one).

## No longer needed

The original direct proof imports
`Sheaf.Paper.RingedTopoiDerivedPullbackIndependent` and
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients` move to the universal
counit lemma. `Sheaf.Algebra.Homology.StrictCoefficientTensorDescent` is imported only by the two
descent lemmas. They remain needed, and no entire module or node is withdrawn.

The original node now depends on the two descent nodes and the unchanged comparison
data node. Its ringed-topos, strict descent and K-flat-resolution dependencies remain
under the universal lemma; finite-change-of-rings normalization remains under the shift
lemma and the public data. Mathlib supplies the total tensor shift sign, naturality,
zero/addition coherence, and preservation of shifted acyclicity. No additional bespoke
sign or inverse-shift lemma is needed. No top-level tool approval was removed.

## Where the brief, the DAG or earlier work was wrong

The plan correctly describes the argument. The stated generic ringed-topos and strict
descent lemmas do not themselves package the required counit for the supplied coefficient
calculus, with the exact finite normalization, nor its coherent derived shifts. Those
specializations are the two explicit remaining obligations. Mathlib already contains
the signed unbounded total tensor shift, so that part need not be rebuilt from sums.
The unit route is retained.

## New nodes

`def-pur-sequence-kflat-comparison-data` records the six unchanged data declarations
relocated from the original node. Its source, dependency list, blueprint ancestry and
Lean attachment are recorded in its JSON file.

`lem-pur-sequence-reduction-universal` is the normalized universal counit for the supplied
reduction, with the original proof steps 1–2 and their dependencies. Its docstring
explains the descent and all finite/transition normalizations.

`lem-pur-sequence-reduction-shifts` is the descent of the ordinary identity-on-terms
shift maps, with the original steps 6–7 and their dependencies. Its docstring includes
coherence, comparison and finite evaluation arguments.

Change record: `coord/changes/J8-pur-sequence-kflat-comparison-data.md`.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
