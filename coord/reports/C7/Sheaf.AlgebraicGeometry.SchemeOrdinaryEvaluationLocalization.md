## What changed

Repair of returned head `689fc8ee20`: the reviewer accepted the mathematics, but
landing detected a concurrent change to `ExactSourceEvaluationLocalComparisons`.
The current server has this consumer in quarantine. Its current archive was read
directly and checked equal to the shared archive. The compatibility wrapper was
reapplied to that source, preserving its copyright header, all three public imports,
and its original source/blueprint module documentation. The nine-module restoration
and ten upstream Lean attachments are retained. The delivery tool constructs the
replacement commit on the freshly fetched `sheaf-dag` base.

Repair validation: all nine modules and all nine retained API probes were
recompiled on the server. All eleven public declarations retain their former types
and their axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`.

This is the upstream-sync rework of a zero-hole module, with its eight quarantined
evaluation consumers restored in the same packet. Each restored module now re-exports
its already proved `WeilConjectures.AlgebraicGeometry` twin. The root thereby uses the
fixed K-injective augmentation construction with explicit Hom-complex universes and
avoids the reported `?u + 1 = u` inference failure. The consumer wrappers retain their
former public imports, including `Sheaf.Algebra.Homology.KFlat` where applicable.

Restored modules:

- `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`.
- `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`.
- `Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`.
- `Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels`.
- `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons`.

Ten DAG Lean attachments identify the corresponding upstream declarations and quote
each current signature. Mathematical statements, sources, dependencies, unit routes
and upstream files are unchanged. No target statement is edited.

Change record: `coord/changes/scheme-ordinary-evaluation-upstream-compatibility.md`.

Validation: all nine final modules compile without warnings through `lcompile.py`,
each below 13 seconds. Temporary API probes assign each of the eleven upstream public
constants its former public type, retaining the old K-flat predicate; only the ambiguous
Hom-complex universe parameters are explicit. These checks confirm the K-flat predicate
rename is definitionally compatible. Their `#print axioms` checks show only `propext`,
`Classical.choice`, and `Quot.sound`. The temporary probes are excluded from delivery.

## Proved and sorry left

The item and all eight original cluster modules have zero textual proof holes.
Holes closed: none (0 of 0). Holes added: none. Split-off theorems: none.
Every re-exported theorem is already fully proved upstream, with no reachable
`sorry` according to its axiom audit. This packet repairs and restores their APIs;
it does not count their pre-existing proofs as newly closed holes.

The audited public declarations are:

- `AlgebraicGeometry.schemeOrdinaryHomComparison`.
- `AlgebraicGeometry.schemeDerivedTensorHomEquiv_naturality`.
- `AlgebraicGeometry.schemeOrdinaryEvaluation_localization`.
- `AlgebraicGeometry.exists_kInjective_scheme_evaluation_models`.
- `AlgebraicGeometry.exists_exactSource_kInjective_evaluation_open_models`.
- `AlgebraicGeometry.exists_exactSource_evaluation_open_models`.
- `AlgebraicGeometry.exists_exactSource_evaluation_local_comparisons`.
- `AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_retraction`.
- `AlgebraicGeometry.exists_strictlyPerfect_evaluation_local_section`.
- `AlgebraicGeometry.exists_strictlyPerfect_kInjective_evaluation_comparisons`.
- `AlgebraicGeometry.exists_strictlyPerfect_evaluation_comparisons`.

## No longer needed

The local copies of the public definitions, theorem proofs, and proved private helpers
are unnecessary because the same constructions and proofs exist upstream. The compatibility
paths remain to restore the rework cluster. No global module pruning is claimed.

Removed direct imports, grouped by compatibility module (their upstream counterparts
remain part of the adopted implementation where its proof needs them):

- `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`: `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`, `WeilConjectures.AlgebraicGeometry.CanonicalEvaluationOpenRestriction`, `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`.
- `Sheaf.AlgebraicGeometry.ExactSourceEvaluationOpenModels`: `Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`, `WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential`, `WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationPostcomposition`, `WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`, `WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`.
- `Sheaf.AlgebraicGeometry.ExactSourceKInjectiveEvaluationOpenModels`: `Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels`, `Sheaf.AlgebraicGeometry.OrdinaryEvaluationOverTransport`.
- `Sheaf.AlgebraicGeometry.KInjectiveSchemeEvaluationModels`: `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization`.
- `Sheaf.AlgebraicGeometry.SchemeOrdinaryEvaluationLocalization`: `Sheaf.Algebra.Homology.KFlatResolution`, `WeilConjectures.AlgebraicGeometry.CanonicalDerivedTensorHom`, `WeilConjectures.AlgebraicGeometry.CanonicalTensorHomUncurryLocalizedEvaluation`, `WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula`, `WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationUncurryCalculation`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationComparisons`: `Mathlib.CategoryTheory.MorphismProperty.Retract`, `Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons`, `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FiniteFreeInternalHomExact`, `WeilConjectures.Algebra.Homology.BoundedExactTermHomQuasiIso`, `WeilConjectures.Algebra.Homology.DerivedInternalHom`, `WeilConjectures.Algebra.Homology.HomComplex`, `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`, `WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential`, `WeilConjectures.AlgebraicGeometry.PerfectComplex`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`: `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`, `Sheaf.AlgebraicGeometry.StrictlyPerfectLocalHomComputations`, `WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection`: `Sheaf.AlgebraicGeometry.ExactSourceEvaluationLocalComparisons`, `Sheaf.AlgebraicGeometry.StrictlyPerfectLocalHomComputations`, `WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationDifferential`.
- `Sheaf.AlgebraicGeometry.StrictlyPerfectKInjectiveEvaluationComparisons`: `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalRetraction`, `Sheaf.AlgebraicGeometry.StrictlyPerfectEvaluationLocalSection`, `Sheaf.Paper.DerivedInternalHomRestrictOpen`.

The root's two previous public dependencies are still public dependencies of its
re-exported upstream twin. No mathematical node or unit step is bypassed: all former
proof dependencies remain needed by the same upstream proof route. No upstream
declaration is removed, weakened or replaced by an unproved body.

## Where the brief, the DAG or earlier work was wrong

The return is a concurrent-edit landing failure, with no requested mathematical
correction. At repair time the conflicting live path is absent on both the server
and the shared checkout; its source remains in the quarantine path recorded by
`coord/rework.tsv`. Restoration uses that current archive, rather than treating
the missing path as a withdrawal or deleting the archived declaration.

The generic proof brief describes a module with outstanding proofs, but this queue item
is a quarantined rework cluster. Its original text already had zero holes. The failure
was ambiguous inference for the site/coefficient universes of `homComplex` after the
upstream sync. The corresponding upstream definitions and proofs already fix those
universes and close the entire evaluation chain. The old DAG attachments still pointed
at the quarantined local copies; the delivery points them at the existing proved source.

Restoring the first consumer verbatim reproduced the same universe constraint at
`KInjectiveSchemeEvaluationModels.lean:152`. Explicit universe annotations made it and
the next consumer compile. The following duplicate proof exceeded the per-file limit;
the final implementation uses the existing upstream proof rather than elaborating
that duplicate. The final wrapper modules all satisfy the ordinary 60-second limit.

The initial API probe for the open-model theorem needed the same local additive-functor
instances as the original module; adding that test context checks its actual signature.
The upstream binder spellings sometimes drop a leading underscore; the ten node records
quote those signatures. No remaining caller uses an old named argument, and all tested
proposition types agree definitionally. No mathematical statement was found false.
No new node is required.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
