## What changed

Proved `AlgebraicGeometry.Scheme.cbcRealizationLimitMap_isIso` in
`Sheaf.Paper.CompleteProetaleStrictTowerRealization`. The normalized Roos comparison
is invertible, and its ordinary-limit derived-unit equation identifies it with the
specified constant-diagram mate. The proof uses existing normalization APIs and
adds nine private helpers: two explicit unit constructions and seven proved lemmas.

Added proof-only imports of `ExactEquivalenceDerivedSquares`,
`StrictRoosShiftLocalization`, `NormalizedLimitSquareCoherence`,
`ExactProductFunctorStrictLimit`, `StrictTowerExchangeMateNormalization`, and
`RingedOpenScalarLimitCoherence`. Every existing public import and public signature
is preserved. The realization node records the actual proof dependencies.

Made the essential-image witness in `cbcRealizationScalarOpenInv_isIso` explicit;
the same scalar/open isomorphism directly provides the witness. Profiling showed
large unfolding costs elsewhere in the module. The endpoint module's local
irreducibility settings for derived functors, left adjoints and constant sheaves
are therefore used throughout this namespace; the open adjunction is also locally
irreducible within its invertibility proof. The evaluation section also keeps module pullback and its adjunction locally
irreducible. These settings do not persist for importers. Existing public definition bodies and signatures are unchanged.

Proved the complete limit-mate identification over arbitrary abelian categories,
with the ordinary-limit additivity instances explicit. The ordinary constant/limit
projection calculation is also a proved abstract helper,
`cbcRealizationOrdinaryLimitMate`. The sheaf proof specializes these checked results. Added the proved private lemma
`cbcRealizationRestrictionForgetsProducts` and used it in `cbcRealizationProducts`.
It constructs the identity natural isomorphism of the forgetful composite over
arbitrary ring sheaves, then transports limit preservation. Explicit source and
target rings avoid inference through the adic coefficient data. Profiling measured
this step at 89 milliseconds, down from about 20 seconds. Neither change alters an
existing public statement.

The unused-variable and unused-section-variable style linters are disabled for
these large dependent interfaces, as in `ExactProductFunctorStrictLimit`; all
proof terms remain checked by Lean's kernel. No profiling option or diagnostic
metaprogram remains.

Proof checking runs sequentially (`Elab.async false`), so the final axiom scan
does not contend with pending proof checks. This preserves full kernel checking.

The private proof context and explicit constructions are recorded in
`coord/changes/Y5-normalized-limit-mate-proof.md`.

Validation: the complete module with the exact delivery axiom scan compiled through
`lcompile.py` in 43.7 seconds. The scan reported precisely the two remaining holes
and no disallowed axioms. Diagnostic commands and profiler options were then removed.

## Proved and sorry left

Closed one of the item's three original holes:
`AlgebraicGeometry.Scheme.cbcRealizationLimitMap_isIso`.
No holes added or split off.

The private unit-normalization lemmas `cbcRealizationCochainUnit_eq`,
`cbcRealizationRoosUnit_derived`, `cbcRealizationRoos_normalization`,
`cbcRealizationLimit_cochain_normalized`, and `cbcRealizationLimit_mate_eq`, together
with `cbcRealizationOrdinaryLimitMate` and
`cbcRealizationRestrictionForgetsProducts`, are fully proved. `cbcRealizationCochainUnit` and `cbcRealizationRoosUnit` are
explicit canonical constructions with no holes.

Two original holes remain unchanged, both belonging to
`lem-cbc-complete-proetale-strict-tower-realization`:

- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_open`.

This is a partial proof delivery, not a decomposition. All existing proved
reduction, scalar/open, product, evaluation and naturality results are retained.

## No longer needed

None. No import, module or node is withdrawn. Every added proof import supplies
an API used in the normalization argument. The endpoint transport module remains
needed by the existing reduction/open proof. The original proper/open route
remains for the two untouched holes.

## Where the brief, the DAG or earlier work was wrong

The endpoint module contains the same generic limit-mate argument, but that
private helper was not in the published build used by either local or server
compilation. The assigned theorem therefore follows that existing argument using
the older available normalized comparison and derived-unit APIs. The added
private helpers are proved parts of that argument; there is no replacement hole.

`CompletedOpenStrictMateIdentification` is a stated proof dependency but currently
imports this item module. Directly importing it to prove the remaining ordered open
identity would create an import cycle. Its completed clause also requires completeness
of the extended object, which the standalone open identity does not assume. This
packet preserves those statements and their remaining proof plans.

The generic cochain-unit and strict Roos limit-model results are used as categorical
tools; neither changes the compact-support unit's proper/open proof route.

## Second reading by Y5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
