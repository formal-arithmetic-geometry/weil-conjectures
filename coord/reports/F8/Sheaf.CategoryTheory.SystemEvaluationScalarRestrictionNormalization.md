## What changed

Constructed the ordinary level scalar and transition comparisons from the compatible
ring squares. The new `InverseImageScalarRestriction.exists_comparison` has a complete
proof using preservation of products, the algebraic operation equations and reflection
of underlying isomorphisms. It compiles with zero holes.

Reduced the original composite theorem to two independent intermediate results:
`systemSingletonEvaluationMate` identifies the specified singleton conjugate with the
exact evaluation mate; `systemRestrictionMateCoherence` supplies invertibility and
coherence for restriction mates independently of singleton data. The parent combines
these using the general derived exact mate normalization, adjunction conjugation,
the mate/counit equation and cancellation of the invertible transition comparison.

Moved the existing definitions and structure verbatim into
`SystemEvaluationNormalizationData` so both intermediate modules can state their
results without an import cycle. The original module publicly imports this data module.
No target signature or mathematical definition has changed.

## Proved and sorry left

Original holes: one, `SheafOfModules.systemEvaluationScalarRestrictionNormalization`.
The parent proof is assembled from the two intermediate statements. This is a
decomposition, not a claim that the mathematics is proved without remaining holes.

Added holes:

- `SheafOfModules.systemSingletonEvaluationMate`.
- `SheafOfModules.systemRestrictionMateCoherence`.

The two added holes have nodes `lem-pur-system-singleton-evaluation-mate` and
`lem-pur-system-restriction-mate-coherence`, respectively.

The new theorem `SheafOfModules.InverseImageScalarRestriction.exists_comparison`
is proved with zero holes. No definition contains a hole.

## No longer needed

The parent no longer imports the general tensor-composition comparison route:
`SheafRingDerivedCoefficientAdjunction`, `RingedComparisonTensorAdjunction`,
`KFlatResolutionIndependentCoefficients`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
`RingedTopoiDerivedPullbackIndependent`, and `SystemSingleDerivedEvaluation`.
The corresponding direct parent proof dependencies are replaced by the actual
intermediate statements and `lem-pur-exact-derived-mate`.
The obsolete parent `tool_uses` entries for the former proposed route are withdrawn;
no maintainer approval is added or replaced.

No existing source declaration or module is withdrawn. The ringed composition theorem
remains needed by the unfinished restriction-coherence intermediate. The singleton
intermediate retains the normalized extension and geometric comparison dependencies.
The existing public imports remain available through the shared data module.

## Where the brief, the DAG or earlier work was wrong

The original plan's general ringed-site theorems are written using small sites with
common universes, while this item retains independent site universes. The restriction
comparison proof was generalized directly using the algebraic graph equations.
The two remaining steps are stated with the exact varying-ring system functors;
no preservation of K-injectives by evaluation or scalar restriction is assumed.

An earlier draft report in the sandbox claimed complete proof before successful
compilation. That claim is withdrawn; the actual hole count above is authoritative.
The abandoned restriction implementation is preserved only in scratchpad. The
singleton derivation keeps the original choice term behind a named irreducible
definition, exposing its fixed ordinary fields without expanding the construction.
This representation repair is recorded in systemSingleDerivedExtensionFields.md.

## New nodes

- `def-pur-system-evaluation-normalization-data`: unchanged data moved out of the parent.

- `lem-pur-inverse-image-scalar-restriction-comparison`: proved ordinary comparison.
- `lem-pur-system-singleton-evaluation-mate`: singleton normalization identification.
- `lem-pur-system-restriction-mate-coherence`: independent restriction-mate coherence.

Change records: `coord/changes/systemEvaluationNormalizationData.md` and
`coord/changes/systemSingleDerivedExtensionFields.md`.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
