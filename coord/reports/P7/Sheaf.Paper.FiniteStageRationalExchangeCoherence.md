## What changed

Filled the proofs of `CategoryTheory.ScalarLocalization.between_karoubi_spec` and
`CategoryTheory.Idempotents.additive_karoubi_extension_spec` in
`Sheaf.Paper.FiniteStageRationalExchangeCoherence` without changing their statements.

The localization proof uses the existing `betweenHom` linear map: its additivity
and `LinearMap.baseChange_tmul` give the two assertions directly. The Karoubi
proof computes the existing extension on objects and arrows, proves its
additivity, and uses naturality at the projector and idempotence to insert the
second projector. The same calculation applied to an isomorphism and its inverse
gives both supported formulas. At the identity projector, explicit equalities
of the endpoint Karoubi objects and extensionality of supported arrows prove the
stated heterogeneous equality. This works for arbitrary projectors, including
zero and identity, without extra hypotheses.

The full geometric coefficient-coherence theorem remains unchanged. This is a
partial proof delivery for a module containing several holes, with no split-off
statements. The two completed arguments follow the corresponding parts of the
existing node's plan, so no DAG change is needed.

## Proved and sorry left

Closed two of the original three holes:

- `CategoryTheory.ScalarLocalization.between_karoubi_spec`.
- `CategoryTheory.Idempotents.additive_karoubi_extension_spec`.

One hole remains, with its existing source and complete proof plan:

- `AlgebraicGeometry.Scheme.FiniteStageRationalExchange.finiteStageRationalExchangeCoherence`
  (`lem-sbc-finite-stage-rational-exchange-coherence`).

Added holes: zero. New axioms: zero. No definition or theorem signature changed.
The delivery probe compiled both completed proofs in 13.8 seconds. Its unused-section-variable
warning for the original redundant `[G.Additive]` parameter is suppressed locally, preserving
the signature. The final delivery reruns compilation and the axiom/hole probe.

## No longer needed

Removed these unused private proof imports; the completed generic calculations
need only the existing public imports:

- `Sheaf.CategoryTheory.SemilinearScalarLocalization`.
- `Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer`.
- `Sheaf.Paper.CondensedAmbientExchange`.
- `Sheaf.Paper.RingedPushforwardCompletion`.
- `Sheaf.Paper.PbcQbarCompletedPullback`.
- `Sheaf.CategoryTheory.ReflectedCompositorUnitNormalization`.
- `Sheaf.CategoryTheory.ReflectorSquareMateFactorization`.

The direct base-change-of-Hom calculation avoids semilinear extension machinery
for `between_karoubi_spec`. This does not establish that these nodes are
unnecessary for the remaining geometric theorem: its existing proof plan and
its dependency records are retained. No module is withdrawn and no mathematical
DAG dependency is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

No statement discrepancy found in the two proved assertions. The theorem named
`between_karoubi_spec` describes the raw localization functor; its proof does not
need Karoubi extension or the identification of the localized ring with a finite
coefficient field. For the identity-projector clause of the Karoubi theorem,
functorial preservation of identity must identify endpoint objects before
converting equality of underlying arrows to the required `HEq`.

The main theorem still requires the comparison of the two completed coefficient
maps (the `pbcCompletedScalarMap` and `pbcScalarCoefficientMap` presentations),
the specified integral push/pull model transports, coefficient-unit
normalizations, and their tower and exchange compatibility. Scheme-identity
coherence in `pbcScalarOperations_identity` is not by itself the equal-coefficient
unit normalization required here. Those remaining obligations have not been
replaced by unproved new declarations or arbitrary comparison choices.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
