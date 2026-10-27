## What changed

Completed three existing theorem proofs in
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`, with five proved private helpers.
All existing declaration signatures, definitions, public attributes and imports are preserved.
The owning node's proof plan now records the arguments actually used.
Local irreducibility attributes on `ScalarLocalization.category`, the cached stage
category, and the specialization Hom group structures avoid expanding category
and additive data during elaboration; they change no exported definition.

For `transportSystem`, the cocycle gives idempotence of reflexive transport.
The normalized tensor unit makes the reflexive stage transition faithful, so
`StageSystem.tr_injective` makes transport injective. An injective idempotent
is the identity. `StageSystem.tr_tr` supplies the composition law.

For `specialization_transitionShift`, uniqueness of the integral normalization
identifies the integral shift witnesses for the two proof parameters. Equality transport
through the localization functor identifies their images. Their rational
normalizations therefore agree at one; uniqueness identifies the coherent rational
shift structures.

For `specialization_additive`, the specialization equivalence preserves zero objects
and binary products. Apply Mathlib's
`Functor.additive_of_preserves_binary_products` to the prescribed preadditive
structures. No explicit calculation of sums of representatives is needed.

An unchanged copy of the current `SfAlgebraicallyClosedCoefficients` is present
only as compile context; that module has no source changes.

Repair of returned head `fdb6ce4b573`: the landing rejected overlapping edits after
`a62c78b1fa2` removed the earlier batch. Started from the current shared source and
reapplied only the three K2 proofs and their three proved private helpers. The
rolled-back structural-instance changes and four F7 hole-closing proofs stay out. The node likewise starts from its current record and retains
all current metadata and proof steps before adding the three K2 arguments.

The post-rollback source compiled in 65 seconds with the three added proofs.
Profiling showed repeated expansion of concrete category data. Refactor the already
proved `transport_additive` and `composition_bilinear` through two proved private
lemmas over abstract categories, preserving both theorem statements and the original
calculations. No definition or consumer is adapted.

## Proved and sorry left

Closed three of the current fourteen holes, adding zero holes and zero split-off statements:

- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.transportSystem`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_transitionShift`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_additive`.

Eleven current named theorem holes remain, all with node
`def-weil-algebraically-closed-coefficients`:

- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.transitionCommShift_existsUnique`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.transitionExact`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.associator_cocycle`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.shift_existsUnique`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.transitionIso_commShift`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_comparisons`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_pairs`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_transport`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_homCoordinates`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_commShift_existsUnique`.
- `WeilConjectures.GeneralAlgebraicallyClosedCoefficients.specialization_distinguished`.

Their original statements, source docstrings and complete proof plans are retained.
The finite-field dependency's eighteen existing holes are unchanged; none is added
or closed by this delivery. Every new private helper is proved without `sorry`.

## No longer needed

No import, module or node is withdrawn. The existing construction and remaining
obligations still require the declared dependencies. The additive specialization
proof no longer needs its earlier proposed representative-sum calculation. The
transport identity proof no longer needs a separate calculation of the two unit
coherence equations: faithfulness and the existing cocycle suffice.

The unit `sk-def-sf-operations` has no additional realized proof steps, and its route
is preserved. No adopted source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found in the assigned declarations.
The stage-system API already proves successive transport composition, and its
injectivity criterion plus the existing tensor unit gives a shorter proof of the
reflexive transport law. Mathlib's categorical additivity criterion similarly
replaces the proposed elementwise specialization argument.

Searches used LeanFinder for directed-system composition, Loogle for
`DirectedSystem.map_self`, and the prescribed grep search for
`Functor.Faithful.of_iso`, followed by local reads of the stage-system and
additive-functor APIs. No new public mathematical statements or nodes were introduced.

The attempted generic coordinate comparison proved representative induction, but its
concrete instantiation expanded cached scalar-localization group structures beyond
the heartbeat limit. That attempt and its unused helper are excluded; the original
coordinate theorem remains unchanged as a named obligation.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
