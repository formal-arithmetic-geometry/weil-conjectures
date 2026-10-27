# IntegralAmbient tensor comparison elaboration

## Reason

Chosen coefficient rings, scalar-extension witnesses and monoidal structures caused repeated
large reductions. Proofs now use section-local irreducibility and their proved generator APIs.
The independent coefficient monoidal instance is installed locally, and redundant imported
cochain instances are disabled while this module is elaborated. No public attribute or public
import changes.

## Old

The original irreducibility block followed the operation-unit definitions and made the
coefficient, pullback and tensor comparisons irreducible only there.

## New

Irreducibility is installed before the comparison proof. The proof uses scalar-extended total
summand extensionality. `coefficientTotalTensor` is restored to semireducible for `tensor_good`
and the representative definition, as required by their existing construction, then kept
irreducible for the final large statement. Private helpers are proved. No definition has a hole.

## Users

These commands and private helpers affect elaboration of the item only. The separately recorded
canonical functor annotations have their complete consumer table in
`coord/changes/G2-integral-ambient-push-category.md`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralAmbientOperationModels | G2 | Proof elaboration only. |

## Status

landed 20261024T210831-L-42281 2026-10-24 (merge of deliver/G2/Sheaf.Paper.IntegralAmbientOperationModels)
