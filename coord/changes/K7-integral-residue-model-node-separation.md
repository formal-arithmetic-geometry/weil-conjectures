# WeilConjectures.OpenDvrCoefficientModel / OpenDvrOpenModel node separation

## Reason

The existing definition node grouped coefficient and completion structures together with
OpenDvrOpenModel. Its dependency on open tensor normalization belongs only to the open
structure. Reusing the already proved coefficient-only intrinsic criterion below the
stratum input would therefore create a DAG cycle through unrelated extension-by-zero
results. This repair separates the existing declarations at the node level. No Lean
file outside the item and its new helper modules is changed; no signature, data,
visibility, attribute, instance or import changes. No target meaning changes.

## Old

Existing bundled node statement, verbatim:

Fix the prime, finite extension, valuation ring, small pro-etale coefficient categories and adic datum of [def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-site, def-weil-pbc-adic-coefficient-datum]. OpenDvrCoefficientModel consists of finite-constant and limit-projection-normalized coefficient ring isomorphisms and their actual scalar restriction equivalence. OpenDvrCompletionModel records simultaneous quotient towers, normalized total limits, strict K-flat augmentations, the specified Koszul and intrinsic unit equations and the quotient-completeness criterion. OpenDvrOpenModel records finite-constant-normalized and completed-projection-normalized open restriction of coefficients, actual scalar restriction equivalence and the exact open-extension adjunction of [lem-sf-open-tensor-normalization]. The coefficient and completion structures retain the complete normalized comparisons as fields, rather than arbitrary isomorphisms of objects.

Existing definition signatures, unchanged:

```lean
structure OpenDvrCoefficientModel
    (d : AdicCoefficientDatum (Padic.coefficientExtensionIntegers l E))
    (T : Scheme.{u})

structure OpenDvrOpenModel {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
```

The original node attached both OpenDvrOpenModel and OpenDvrOpenModel.jShriek,
and included lem-sf-open-tensor-normalization among its statement dependencies.

## New

The original node retains coefficient/completion declarations and now states:

Fix the prime, finite extension, valuation ring, small pro-etale coefficient categories and adic datum of [def-weil-l-adic-coefficient-extension, def-weil-pbc-proetale-site, def-weil-pbc-adic-coefficient-datum]. OpenDvrCoefficientModel consists of finite-constant and limit-projection-normalized coefficient ring isomorphisms and their actual scalar restriction equivalence. OpenDvrCompletionModel records simultaneous quotient towers, normalized total limits, strict K-flat augmentations, the specified Koszul and intrinsic unit equations and the quotient-completeness criterion [def-weil-derived-complete, prop-weil-pbc-koszul-reconstruction, lem-coef-derived-system-evaluation-calculus]. These coefficient and completion structures retain normalized comparisons as fields. The separate OpenDvrOpenModel interface is recorded in its own definition node.

The separated existing-declaration node def-sf-open-dvr-open-model states:

Fix a prime and finite coefficient extension [def-weil-l-adic-coefficient-extension] and a scheme open immersion on the small pro-etale sites [def-weil-pbc-proetale-site]. OpenDvrOpenModel records finite-constant-normalized and completed-projection-normalized open restriction of the completed integral coefficients [def-weil-derived-complete], actual scalar restriction equivalence, and the exact open-extension adjunction [lem-sf-open-tensor-normalization]. Its jShriek is the derived scalar equivalence followed by the exact derived extension. This is the existing open part of the former bundled model node, without any change to its data or normalization.

Its Lean attachment is the existing OpenDvrOpenModel and its jShriek; neither moves
in Lean. OpenDvrRingedIdentification cites that node. OpenDvrIntrinsicOpenTransport
cites both it and the original coefficient/completion node.
The assembly OpenQuotientKoszulCompleteness cites both nodes. All other original
citers retain their coefficient/completion citation. Statement-change records list
every original citer and confirm the unchanged Lean meaning.

## Users

Ran tools/downstream.py on OpenQuotientKoszulModels with --uses OpenDvrOpenModel.
Its four textual users are the models module, RingedIdentification,
IntrinsicOpenTransport and OpenQuotientKoszulCompleteness, all listed below.
The following also lists every original DAG citer with a Lean module. Claim records
for changed existing nodes were absent. No consumer needs a Lean adaptation or a
compatibility recompile, since the entire Lean interface is identical.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.OpenDvrRoosCompletionComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrRingedIdentification | unclaimed | Open-model citation redirected; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrIntrinsicOpenTransport | unclaimed | Open-model citation redirected; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrAugmentedReductionComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrDerivedTowerComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrStrictReductionComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrIntrinsicCriterion | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenQuotientKoszulCompleteness | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrLimitComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrOrdinaryTensorTransport | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenDvrAugmentedTowerComparison | unclaimed | Existing coefficient/completion citation remains valid; all Lean unchanged. |
| Sheaf.SixFunctors.OpenQuotientKoszulModels | unclaimed | Only node attachment grouping changes; no Lean edit. |

## Status

landed 20261027T034706-L-3674777 2026-10-27 (merge of deliver/K7/Sheaf.Paper.IntegralResidueStratumInput)
