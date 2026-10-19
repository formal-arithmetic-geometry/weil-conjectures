## What changed

Implemented `WeilConjectures.field_tor_amplitude` in `Sheaf.Paper.FieldTorAmplitude` without changing its signature or public imports. Added the proof-only import `Mathlib.Algebra.Field.ULift` for the lifted field instance. The two boundedness fields of the specified ordinary realization provide ordered intervals. A proved private helper transfers those intervals through every representative/resolution test in `HasProEtaleTorAmplitude`. It uses the existing constant-field tensor-cohomology theorem, proves the natural identification of the two existing sheaf tensor presentations, and applies the proved single-factor total-tensor comparison. The tensor comparison composes the sheafification counit, the right tensor functor, the monoidal functor comparison, and the sectionwise presheaf tensor isomorphism. Explicit types and the existing zero-preservation instance keep its elaboration within the file limit. There are no new definitions or public statements. The private proof-context commands are recorded in `coord/changes/D3-field-tor-amplitude-proof-context.md`.

## Proved and sorry left

The proof closes the one original hole: `WeilConjectures.field_tor_amplitude` (node `lem-weil-field-tor-amplitude`). No holes added or split off. No `sorry` remains in the delivered module. The final proof compiled remotely; delivery preflight verifies it again with the axiom probe. The ordinary realization existence theorem remains an existing dependency of the statement; this delivery does not claim to prove it.

## No longer needed

Removed proof imports `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`, `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`, `Sheaf.Paper.FiniteTorAmplitudeSites`, and `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`. No new resolution is chosen: the recorded predicate already quantifies over all K-flat resolutions. Thus the proof no longer needs node `lem-pc-kflat-resolution`; its proof dependency and obsolete tool approval were removed from the node copy. The other three removed modules provide different coefficient/site presentations unused by this statement. Existing public imports are retained to preserve the importer-visible interface. Global reachability of these modules through other imports is not claimed to disappear.

## Where the brief, the DAG or earlier work was wrong

The plan's instruction to choose a resolution is unnecessary for the actual universal resolution predicate. The proof works with its arbitrary quantified resolution instead. The recorded derived-tensor node currently attaches the fixed-ring sheaf presentation, whereas this statement uses the intrinsic ringed-site `Scheme.derivedTensor` already exposed by `ProEtaleTorAmplitude`; the proof unfolds the actual recorded predicate and uses that construction. The unit record has no realized statement or step bypassed by this change. No mathematical statement was changed and no new node was needed.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
