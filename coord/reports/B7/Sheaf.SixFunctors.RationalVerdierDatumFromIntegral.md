## What changed

Replaced the single unfinished proof of
`WeilConjectures.RationalVerdier.datum_of_integral_kflat` with an explicit construction
of every field of the original rational Verdier datum. Its signature, public imports,
and existing definitions are unchanged. All added imports in the item are proof imports.
No existing module other than the assigned item was changed. The original unused
K-flat witness names are retained; a theorem-local linter setting suppresses their
pre-existing statement-only unused-name warnings.

Six new modules isolate proved parts of the construction:

- `Sheaf.CategoryTheory.ScalarLocalizationBiduality`: localizes a prescribed integral
  biduality, with its actual components, using the existing normalized natural-iso theorem.
- `Sheaf.SixFunctors.RationalVerdierLocalizedCore`: constructs the rational dual by
  fixing the second argument of the existing permitted-pair internal Hom. Proves the
  exact object, scalar-linearity, additivity, and pure-tensor map specifications.
- `Sheaf.SixFunctors.RationalVerdierCompletion`: descends the ratio of ordinary tensor
  comparisons through good-complex localization, then composes with the existing
  normalized completion comparison. Proves its precise chain representative equation.
- `Sheaf.SixFunctors.RationalVerdierSignedKFlat`: proves uniqueness of signed swaps on
  literal K-flat pairs from their pure-tensor formulas; transfers naturality from the
  already constructed natural signed symmetry to the symmetry in the supplied datum.
- `Sheaf.SixFunctors.RationalVerdierLocalizedExact`: restricts the supplied ambient shift
  and triangle hypothesis, then descends exactness through the opposite localization.
- `Sheaf.SixFunctors.RationalVerdierLocalizedEvaluation`: constructs evaluation from
  inverse completion and the ordinary counit. Proves the completed integral square by
  cancellation and the rational square by induction on tensor-product Hom groups.

The original proof node records this actual route. The new constructions choose no
arbitrary object from a mere existence statement: internal Hom is the existing unique
extension; evaluation is an explicit composite; completion uses the existing normalized
chain map and a fully faithful preimage of its prescribed comparison.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.RationalVerdier.datum_of_integral_kflat`
(`lem-coef-rational-verdier-datum-kflat`). No new holes are introduced; no `sorry` remains
in any delivered Lean module. This is a proof from existing stated dependencies, not a
transfer of the obligation to renamed or repackaged hypotheses.

Also proved:
`CategoryTheory.ScalarLocalization.biduality`,
`WeilConjectures.RationalVerdier.localizedDual_spec`,
`WeilConjectures.RationalVerdier.completion_exists`,
`WeilConjectures.RationalVerdier.signed_kflat_natural`,
`WeilConjectures.RationalVerdier.localizedDual_exact`,
`WeilConjectures.RationalVerdier.localizedEvaluation_source`, and
`WeilConjectures.RationalVerdier.localizedEvaluation_natural`.

Existing dependencies may retain their own named holes. In particular ordinary
first-variable counit naturality is used through the existing theorem
`IntegralHom.evaluation_naturality`; it is neither restated nor reproved here.

## No longer needed

No existing module or node is withdrawn, and no original import is removed. The four
original planned dependencies remain used transitively through the construction and
its existing model definitions. The original node's direct proof dependencies now name
the six proved construction lemmas and the integral model, rather than treating all
localization and normalization glue as a single informal step. This does not claim
that the original integral theorem, rationalization, tensor completion, or operation
modules have become unnecessary.

## Where the brief, the DAG or earlier work was wrong

The original node compressed several separate obligations into one step. The existing
`SignedSymmetry` record supplies normalized representative components but no naturality
field; the proof therefore establishes uniqueness on K-flat representatives before
using the existing natural symmetry. Similarly, an arbitrary ordinary presentation
cannot be identified definitionally with the completion theorem's presentation; their
ratio must descend through the good-complex localization.

The ordinary source and target objects of localized operations are prescribed by
propositional equality. The proof keeps those equations and uses HEq only to transport
arrows between equal endpoints. It does not replace the required formulas by arbitrary
isomorphisms. Generic categorical helpers keep these calculations from unfolding the
large geometric definitions during elaboration.

The current server queue was checked before work: the assignment was a proof-route
item, with no rework entry or build-error repair. No original statement was disputed
or changed. The unit route is preserved. Searches used leanfinder for scalar localization
of integral contravariant duality and biduality, loogle for
`CategoryTheory.Functor.rightOp`, grep for `ScalarLocalization|braiding_naturality`, and
local rg searches of both project roots. They found reusable opposite, localization,
and normalized-comparison APIs, but no existing theorem assembling this datum.

Edge cases are retained: the generic categorical calculations allow zero objects and
arrows and localization that kills an object. The signed generator argument uses no
boundedness, nonzero coefficient, or nonempty-site hypothesis. Neither exactness nor
evaluation uses faithfulness of scalar localization. The only dual-constructibility
assumption is exactly the preservation clause already present in the supplied integral
conclusion.

## New nodes

`lem-coef-scalar-localization-biduality` records the proved generic localization of the
specified integral biduality, including the normalized component equation.

`lem-coef-rational-verdier-localized-core` records the actual fixed-second-argument
construction and its four specifications. Its public definitions are `dualInput` and
`localizedDual`.

`lem-coef-rational-verdier-completion` records the proved normalized completion structure
for a supplied ordinary presentation.

`lem-coef-rational-verdier-signed-kflat` records the proved K-flat naturality equation for
any supplied normalized signed symmetry.

`lem-coef-rational-verdier-localized-exact` records the proved restriction and localization
of the supplied integral shift-and-triangle exactness clause.

`lem-coef-rational-verdier-localized-evaluation` records the explicit integral and rational
evaluation constructions, their source equality, and the proved naturality square.

There are no change records: no existing statement, definition, attribute, instance,
or public import was changed, and no forced adaptation was needed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.ScalarLocalizationBiduality": "c58db51fca03769789177b429e438246abba739a", "Sheaf.SixFunctors.RationalVerdierCompletion": "f5748b689fe47298f25c71f6e02d1c464485c9a6", "Sheaf.SixFunctors.RationalVerdierDatumFromIntegral": "062873a433020b9ad14db003e012afe66077c93c", "Sheaf.SixFunctors.RationalVerdierLocalizedCore": "c62413d7cedf47d98aafbca6d55b315578a7b586", "Sheaf.SixFunctors.RationalVerdierLocalizedEvaluation": "2be0d4ec3cd5a4e638140f5b0a94e7907aa123b3", "Sheaf.SixFunctors.RationalVerdierLocalizedExact": "3fd943f26eaa2ad89b23c5fa5fe9f250f475d79f", "Sheaf.SixFunctors.RationalVerdierSignedKFlat": "95ac20dcb46b37935dd58de56df3f145be136b52"}, "results": {"Sheaf.SixFunctors.RationalVerdierDatum": {"hash": "164615386e1467e18c23406d7a9b67282fff944c", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T07:05:48+0800", "transitive": 0, "version": 1}
```

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
