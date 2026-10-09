# Delivery report: `lem-weil-pbc-regular-local-maximal`

## Changes

- Split the target using More on Algebra, Stacks Tag 07C0.
- Added the public supporting node `lem-weil-pbc-regular-ring-local-criterion` for the Tag 00OD regular-ring local criterion.
- Added the public Mathlib leaf `lem-weil-pbc-flat-map-local-criterion` using `RingHom.Flat.propertyIsLocal` and `RingHom.Flat.ofLocalizationPrime`.
- Corrected `created.item` on the target and recorded the three proof steps and `split_report`.

## Proof obligations

The proof has no Lean code and no `sorry`. It follows the 07C0 proof: flatness is local by Tag 00HT; geometric regularity of the fibres is checked after localization using the Tag 00OD criterion; and prime and maximal target localizations are equivalent by further localization. The new regular-ring criterion is intentionally `unsplit` because it is the reusable Stage 1 statement that remains to be proved from the cited source.

## Sources and searches

The target source is `literature/stacks-project/more-algebra.tex`, Lemma Tag 07C0, with its cited Algebra Definition Tag 00OD and Lemma Tag 00HT. The new nodes record three search modes and exact Mathlib declarations where available. No Lean files were changed.

## Review by E1

I checked the target statement against the live Stacks Tag 07C0 page: it has the same three conditions, the same Noetherian hypothesis on the target, and the same contracted primes in every localization. The proof steps follow the source's two inputs, flatness locality (00HT) and the regular-ring local definition (00OD), and explicitly explain why fibre regularity survives localization and why maximal ideals suffice. The flat-map criterion is a public Mathlib leaf with its declaration and source line recorded. The regular-ring criterion is public and intentionally remains an unsplit Stage 1 node; it is not hidden inside the target proof. All new node identifiers are unique on the fetched DAG, and no Lean code or compilation was used.
