## What changed

Proved `WeilConjectures.RationalVerdier.extension_unit` in
`Sheaf.SixFunctors.RationalVerdierUnit`, preserving its signature and docstring.
Constructed the integral natural unit from inverse naturality of the completed
scalar comparison and the ordinary tensor unit. Compared the rational scalar
functor on integral representatives, then descended this natural isomorphism
using `ScalarLocalization.naturalIso_of_integral`.

Applied `IntegralHom.evaluation_naturality` to the supplied ordinary presentation,
then the identity specialization of `IntegralFiniteExtension.comparison_cocycles`.
Cancelled the integral dual of the inverse unit and localized. The supplied
`ExtensionProperties`, `Datum.pure` at one, and `Datum.objects` identify the
comparison and both factors, with their endpoints explicitly checked by HEq.

The private `unit_factor` helper uses the proved `NatIso.trans_app` component
equation. A reflexive proof of this same equation hit a kernel timeout; the
categorical equation avoids normalizing a large concrete derived-functor term.
All reducibility annotations are local to this file.

Added only private proved helpers and three private proof imports:
`Sheaf.CategoryTheory.ScalarLocalizationNaturalIso`,
`Sheaf.Paper.IntegralHomEvaluationNaturality`, and
`Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles`.
Updated the item's DAG proof and dependencies to record these existing lemmas.
The localization descent lemma is used as a general categorical tool from another
unit; it does not replace any step of this unit's route.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.RationalVerdier.extension_unit`
(node `lem-coef-rational-verdier-unit`).
There are zero holes left in the item and zero holes added or split off.
The complete module compiled cleanly through `lcompile.py` in 17.4 seconds.
The proof uses existing declared dependencies, including the still-stated
integral cocycle and normalized evaluation-naturality theorems; this is a proof
from existing dependencies, not a claim that their transitive axioms are closed.

## No longer needed

No import or module was removed. The full theorem
`WeilConjectures.coef_integral_finite_extension` (node
`lem-coef-integral-finite-extension`) is not required as a proof dependency:
only its already-separated integral comparison definitions and the coefficient
cocycle theorem are used. Its statement dependency and all existing declarations
remain in place. No new intermediate statements are needed. The raw rational
localization dependency remains in use. No blueprint unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The current server queue lists the item as a one-hole proof task. The historical
rework/build-error records concern a bad import of RationalVerdierModels; the
current item and model sources have been restored. The proof plan was correct,
but did not name the existing normalized evaluation-naturality and raw
localization descent lemmas explicitly. The updated DAG now does so.
The proof covers torsion and zero objects and the empty scheme without using
faithfulness of localization. No statement or shared definition was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierUnit": "e081a603b11fabad18bf5890986d045a22e24cd9"}, "results": {"Sheaf.SixFunctors.RationalVerdier": {"hash": "62aa3761695accb0a49fd85e0ff1a1b1e659896e", "status": "OK"}}, "seconds": 96, "time": "2026-10-28T01:21:41+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
