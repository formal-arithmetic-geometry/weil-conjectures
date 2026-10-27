## What changed

Repair of returned head `3aac00d77a2`: apply the three node corrections from the
reviewer's `8af981332724/fixes` packet. Restore
`def-pur-scalar-extension-tower-data` byte-for-byte to current main, including its
full declaration list and `proof_origin: null`. The new comparison node records
only its four declarations and cites that definition node in `stmt_deps` and its
statement. The composition node's statement citation and statement dependency
also point to the definition node. Reuse the reviewer's corrected change-record
ownership explanation while retaining the refreshed consumer audit. A reviewer
replacement of that record uses the basename
`D2-scalar-tower-comparison-module.change.md`.

In `Sheaf.Paper.ScalarExtensionTowerCoherence`, prove `square` and `composition`
using the existing ordinary scalar/pullback adjunctions and homogeneous total-tensor
generators. Proved private helpers cache the normalized section calculations and
the two composition equations. The original item source is preserved, including
every existing declaration. All original public imports remain public.

Move the unchanged strict comparison construction into the new
`Sheaf.Paper.ScalarExtensionTowerComparisonData`, publicly re-exported by the original
module. The completed `composition` proof is in the new
`Sheaf.Paper.ScalarExtensionTowerComposition`, also publicly re-exported. This follows
profiling and unsuccessful local unfolding/predicate-cache experiments: the complete monolithic proof exceeded the per-file runtime limit.
The original definitions and theorem signatures are preserved. The original definition node retains ownership of the relocated definitions
through the public re-export. The new comparison node records only `sequenceSmall`,
`siteSmall`, `scalarAdditive`, and `comparisons_existsUnique`. See
`coord/changes/D2-scalar-tower-comparison-module.md` for the relocation and consumer audit.

The square transposes through scalar extension and pullback. Both normalized routes
then give the same tensor of scalar-unit pullback sections. The two composition
squares transpose through the successive scalar adjunctions; the prescribed
associator multiplies the two coefficient-one factors. The proof applies equally to
empty schemes and zero complexes, and makes no flatness assumption on quotient maps.

Validation: all seven files pass the server acceptance check in result
`33ed94eb3603f091333b5d23`: the three delivered coherence modules, the three
current direct importers (`CompletedComparisonQuotientRealizationDefs`,
`IntegralComparisonSystemData`, `IntegralScalarPullbackCounitCompatibility`),
and `CompletedComparisonQuotientRealization`. Wrapper timings include queue,
setup, and artifact work; the per-file Lean limit is unchanged. All unchanged
validation copies were removed. No consumer adaptation is included.
A source audit verifies identical public signatures, attributes and non-theorem
bodies across the split modules. All three corrected node files match the
reviewer's fixes exactly; the definition node also matches current main.

## Proved and sorry left

Closed two of the five original holes:

- `WeilConjectures.ScalarExtensionTower.square`.
- `WeilConjectures.ScalarExtensionTower.composition`.

Three original holes remain, all attached to
`lem-pur-scalar-extension-tower-coherence`:

- `WeilConjectures.ScalarExtensionTower.realizationModels`.
- `WeilConjectures.ScalarExtensionTower.scalarExtensionTowerCoherence`.
- `WeilConjectures.ScalarExtensionTower.quotientModels`.

No holes added or split off. Existing proved declarations remain proved.

## No longer needed

The original module's private proof imports of
`IntegralComparisonSequenceSystems`, `IntegralTensorReductionTowerComparison`,
`SystemScalarGenerators`, `CompletedPullbackTensorComparison`, and
`CochainPullbackTensorCoherence` are removed: the moved construction uses the first
four where needed, and its exported data plus its proved private helpers suffice
for the coherence proofs. The new module imports only its sequence-site data,
coefficient fields, geometric inverse image, cochain tensor interface, and the
existing generator/comparison proof modules. All original public imports are retained.

The strict-square and composition arguments do not use
`lem-pur-strict-coefficient-comparison-calculus`
(`Sheaf.SecSmoothPurity.StrictCoefficientComparisonCalculus`); direct normalization
and adjunction injectivity suffice. Remove that direct proof dependency from the
item's plan. Its internal use by other planned dependencies is unaffected.

The direct statement dependencies `def-weil-integral-scalar-extension` and
`def-weil-proetale-inverse-image` are no longer separately listed as proof dependencies
of the strict-calculus assembly step; their definitions remain used through the
existing sequence-system interface and retained statement dependencies.
No module is withdrawn or deleted, and no unit realization is bypassed.

## Where the brief, the DAG or earlier work was wrong

The item module has five original holes. At the original proof-work snapshot, the DAG's dependency
`lem-pur-normalized-scalar-comparison-realization` records
`Sheaf.Paper.NormalizedScalarComparisonRealization`, but that module is absent
from both `lean/` and `quarantine/` in the supplied checkout. The three original
realization/quotient holes are retained; this delivery uses existing generator
interfaces to prove the strict equations without restating that absent theorem.
The rework and quarantine records were checked before the original source was
copied. This repair preserves the current item source and requests no deletion.

## New nodes

- `stage3-pur-normalized-scalar-tower-comparisons`: the already proved
  `comparisons_existsUnique`, the size instances `sequenceSmall` and `siteSmall`,
  and `scalarAdditive`, in `Sheaf.Paper.ScalarExtensionTowerComparisonData`.
  The relocated definitions retain their original definition-node ownership.
  No new hole or mathematical assumption is introduced.

- `stage3-pur-scalar-tower-composition`: the original `composition` statement and
  its completed proof, in `Sheaf.Paper.ScalarExtensionTowerComposition`, publicly
  re-exported by the original module. This introduces no hole or new assumption.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
