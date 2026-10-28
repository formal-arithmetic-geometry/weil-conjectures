## What changed

Repair of return C-7aed6 (7aed6bc563b), points D1/D2 and 2b. Removed the vacuous `completion_signed_representative_core` theorem and the relocated `completedSignedSwapCore` definition. The item's `completedSignedSwap` is again its original `def`, with its original body and public imports. Removed the importer adaptation; no changes to `RationalVerdierCompletedInterchangeCanonical` are included.

The replacement reduction has two mathematical obligations. `tensor_tower_signed_coordinate` compares scalar extension of a signed ordinary map with the explicit coherent signed swap at a single finite quotient; it concerns finite complexes, without completion or localization. `tensor_roos_signed_model` identifies Roos of the explicit strict coherent swap with the coherent derived braiding through the reference tensor models; it contains neither an ordinary tensor augmentation nor an arbitrary map s. These are separate steps, not the item composed with an isomorphism.

The item proves the intervening argument: identify the choice-defined completion chain with the existing normalized augmentation by its pure quotient and zero shifted coordinates; assemble finite component equalities by natural-transformation extensionality; use Roos-unit naturality to obtain the chain square; localize it and conjugate through the full tensor-model normalization. The mapping-fibre square follows by functoriality of the actual Roos model, so no new unproved assertion about a shifted coordinate is added.

## Proved and sorry left

The item theorem `WeilConjectures.RationalVerdier.completion_signed_representative` is reduced to the two obligations above. This is a decomposition, not an independent proof of the original mathematical assertion: one original hole is closed and two strictly smaller holes are added.

- `WeilConjectures.RationalVerdier.tensor_tower_signed_coordinate`, node `lem-coef-rational-verdier-tensor-tower-signed-coordinate`: one named `sorry` for the finite quotient signed-generator calculation.
- `WeilConjectures.RationalVerdier.tensor_roos_signed_model`, node `lem-coef-rational-verdier-tensor-roos-signed-model`: one named `sorry` for the coherent braiding/strict Roos representative normalization.

The completion-chain identification, the naturality assembly, and the isomorphism-conjugation algebra have complete Lean proofs. The definition `strictTensorSignedSwap` is an explicit composition of existing tower isomorphisms and the restricted coherent signed chain swap, with no unproved data selection.

## No longer needed

Removed the returned module `RationalVerdierCompletionSignedRepresentativeCore`, its vacuous theorem and duplicated swap definition, and its node from this replacement packet (none is on current main). Removed its public import and the unforced downstream dsimp adaptation. No existing library module is withdrawn.

The original mathematical model dependencies remain needed, either in the two genuine split statements or in the proved completion-chain identification. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The return correctly identified the previous split as a restatement: postcomposing an equality with an isomorphism does not simplify its mathematical content. The previous report's claim that it was strictly simpler was wrong. This repair replaces it with the finite-quotient calculation and the independent coherent-model identification, and supplies the genuine Lean argument joining those steps to the unchanged item statement. It also restores the public swap interface exactly as point 2b requires.

## New nodes

`lem-coef-rational-verdier-tensor-tower-signed-coordinate`: the scalar-extension signed square at one finite quotient, including the explicit strict coherent tower swap construction. Source: the blueprint signed-transposition paragraph and Stacks 03EL, 06YL, 07A4, 0941. Searches found generic graded tensor operations and existing tensor-tower normalization, but no theorem giving this specific normalized finite square.

`lem-coef-rational-verdier-tensor-roos-signed-model`: representative normalization of the coherent derived braiding through the strict Roos tensor model, with no ordinary-to-completed augmentation. Source: the same blueprint paragraph, the coherent braiding representative equation, and Stacks 06YL, 08TC, 0941. Existing Roos-unit naturality and the full tensor-model normalization are reused in the item; the coherent braid/model equation is the remaining separate obligation.

`lem-coef-rational-verdier-completion-chain-normalization`: proved identification of the chosen completion chain with the existing native chain from their two recorded coordinates. It provides a small API lemma for the choice-defined map and keeps its expensive type checking in a self-contained module.

`lem-coef-rational-verdier-completion-chain-naturality`: proved conditional naturality for any strict tower square. It uses the normalized chain identification and the existing Roos-unit naturality; it contains no Koszul-sign assertion. Its generic composition proof is complete.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierCompletionChainNaturality": "f452f25b1bc8004ac11389af1114a7ef2775b85b", "Sheaf.SixFunctors.RationalVerdierCompletionChainNormalization": "d7ddf0c772c0ee040862d2cf6e1047b134c7448a", "Sheaf.SixFunctors.RationalVerdierCompletionSignedRepresentative": "cc881342fb297c68e618d1aa95152e1e85474523", "Sheaf.SixFunctors.RationalVerdierTensorRoosSignedModel": "d5ed196404ac2842a69d84446d87d143ea2f28c5", "Sheaf.SixFunctors.RationalVerdierTensorTowerSignedCoordinate": "3b819f41841957b3f2a6b8add0aee82b7a04ea78"}, "results": {"Sheaf.SixFunctors.RationalVerdierCompletedInterchangeCanonical": {"hash": "6b558637359e00f66eaca1d59cc74ba03eb4baac", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T13:39:28+0800", "transitive": 0, "version": 1}
```

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
