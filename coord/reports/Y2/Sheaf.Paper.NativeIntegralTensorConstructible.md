## What changed

Replaced the single proof hole in `Sheaf.Paper.NativeIntegralTensorConstructible` by a
complete Lean reduction through ordinary coefficient extension. The public statement
and its public import are unchanged. All added imports in this module are private.

The proof uses `integralStratifiedPerfectDetailed` and
`integralStratifiedPerfectCharacterization` to obtain bounded integral cohomology with
stratified finitely presented local models. Faithfulness of ordinary coefficient
restriction is proved directly on sections. A proved private helper transports the
local-model predicate along an isomorphism. The scalar-extension adjunction proves
finite-colimit preservation. Uniqueness of universal left derived functors identifies
`pbcDerivedExtend` with termwise exact extension. Two homology comparison isomorphisms
then reduce each degree to the ordinary sheaf assertion, and the section equivalence
reflects boundedness.

Added two independent ordinary coefficient obligations, each in its own module:
`NativeIntegralCoefficientFlat` concerns finite-limit preservation for all modules;
`NativeIntegralCoefficientHeart` concerns constructibility of one ordinary sheaf with
finite local integral presentations. Neither states the assigned derived theorem,
repackages its hypothesis, or quantifies over derived input/output complexes.

Validation: the three modules compiled together in import order through `lcompile.py`.
The assigned module compiled in 10.4 seconds. The flatness statement was subsequently
restricted to Noetherian schemes to match the existing condensed coefficient calculus;
the final delivery recompiles this version. No existing definition, instance, attribute,
or public signature was changed. No consumer adaptation is needed.

## Proved and sorry left

This is a decomposition, not a completed proof of coefficient constructibility or a
claim of net hole reduction. One original hole is closed by a compiling Lean argument:
`WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralTensor_constructible`
(node `lem-sf-native-integral-tensor-constructible`). There is no `sorry` left in the
assigned module. Its conclusion still depends on the two new obligations below and
on the existing integral-characterization theorem.

Two holes are added, both public named theorems with proof exactly `:= by sorry`:

- `WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralCoefficient_flat`,
  node `lem-sf-native-integral-coefficient-flat`, module
  `Sheaf.Paper.NativeIntegralCoefficientFlat`.
- `WeilConjectures.LocallyFiniteAdicRealization.nativeIntegralCoefficient_heart`,
  node `lem-sf-native-integral-coefficient-heart`, module
  `Sheaf.Paper.NativeIntegralCoefficientHeart`.

Thus the submitted files have two remaining holes, versus the item's original one.
The new statements contain no data choices and no definitions with postponed data.
The colimit half of ordinary exactness is proved in the assigned module rather than
included in the new flatness obligation.

## No longer needed

No original import is removed: the original module had only its statement import
`Sheaf.Paper.LocallyFiniteAdicRealizationData`, which remains public. An exploratory
import of `Sheaf.Paper.IntegralCoefficientCompletenessTransport` was removed; direct
faithfulness of ordinary restriction suffices for the proof written here.

`lem-per-continuous-rational-derived-realization`
(`Sheaf.Paper.ContinuousRationalDerivedRealization`) is no longer a dependency of this
argument: exact ordinary extension and homology comparisons replace the rational
complex realization step. It is not imported. The new ordinary obligations also do
not require that derived-realization theorem.

`lem-weil-pbc-condensed-flat-coefficient-calculus` is no longer a direct dependency
of the assigned theorem, but remains needed by the new flatness node; it is not
claimed as pruned. No global module withdrawal or global pruning is claimed.
The unit's statement and route are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier plan is mathematically compatible with the conclusion. It needlessly
carries perfect complexes through the final coefficient comparison: the declared
integral characterization already supplies boundedness and stratified finitely
presented cohomology, so a degree-zero coefficient comparison suffices. The revised
node records the exact-functor argument actually written in Lean.

The existing continuous integral encoding and condensed flat coefficient calculus
are useful but do not directly apply to the arbitrary normalized presentation C in
the assigned statement. The missing work is the normalized ordinary scalar comparison
and its local models, now stated explicitly by the two smaller nodes. I did not claim
these existing declarations were absent, prove a weaker replacement for the item,
assume a normalized constructible realization, or add finite-field-scheme hypotheses.

Checked the new assertions mathematically on empty schemes, empty strata, the zero
module, pure uniformizer-torsion local models, nonzero free local models, and varying
finite rank on different strata. Localization kills torsion and sends finite scalar
presentations to finite-dimensional vector spaces. Neither new statement requires a
positive rank, a nonempty cover, dimension bounds, or invertibility of ell on X.

Read Bhatt--Scholze Section 6.8 in the supplied PDF: Lemma 6.8.2, Definitions 6.8.3,
6.8.6 and 6.8.10, Proposition 6.8.11(3), and Proposition 6.8.14(2). The new degree-zero
assertion uses their actual ordinary finite-presentation definition. The source
library `lean/WeilConjectures` was not changed.

## New nodes

`lem-sf-native-integral-coefficient-flat`: ordinary extension along the normalized
completed-integral-to-native coefficient map preserves finite limits. Its proof plan
factors through continuous localization and exact extension from a finite coefficient
field, and uses the normalized internal-section scalar adjunction to identify the
actual map. It has no constructibility assumption and no derived-category conclusion.

`lem-sf-native-integral-coefficient-heart`: an ordinary integral module whose fixed
coefficient transport has stratified finitely presented scalar models becomes a native
constructible sheaf under ordinary extension. Its plan uses continuous integral model
encoding, ordinary preservation of local finite presentations, and native encoding's
constructibility equivalence. It has no complex, cohomological bound or integral
constructible derived input.

For each node, targeted LeanFinder, Loogle and Mathlib grep queries were actually run
through `msearch.py`; their results are recorded in its JSON. Project searches found
and retained the continuous integral models, ordinary scalar encoding, local finite
presentation preservation, and native constructibility comparison declarations.
Blueprint searches for `constructible scalar`, `coefficient flat` and `stratified
finitely` found no match. `integral tensor` found four broader nodes, none stating
either ordinary coefficient assertion. The ancestor tool returns None for the assigned
node; the new records retain that fact and record the parent chain and the precise
coefficient-passage step. No change record is required because no existing interface
or definition was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeIntegralCoefficientFlat": "5e74adc14693539cc712ecae35f0ffc4180fcf9f", "Sheaf.Paper.NativeIntegralCoefficientHeart": "6a5ad12a20a612f8d9fe18f7df8fec65d67baa61", "Sheaf.Paper.NativeIntegralTensorConstructible": "e5f23908ad5c3e5db73735f350561d232959aeff"}, "results": {"Sheaf.Paper.LocallyFiniteAdicFunctorDescentImage": {"hash": "456e56444c2bb839b480ce3a6136bf403a0a15f3", "status": "OK"}}, "seconds": 35, "time": "2026-10-28T12:07:26+0800", "transitive": 0, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
