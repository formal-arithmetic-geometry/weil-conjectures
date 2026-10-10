Files written:

- `dag/nodes/sec-smooth-purity/lem-weil-pbc-spread-purely-inseparable-factors.json`: statement split into three proof steps; Mathlib searches found no exact match.
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-power-in-base-after-localization.json`: one new unsplit statement-only child; Mathlib has only the generic-field `IsPurelyInseparable.pow_mem` ingredient.
- `citations.json`: verbatim statement quotes for every cited node in every step.

Attachments: none.

WANTED: the blueprint source file named by the imported node is absent from this checkout; the proof follows the imported finite-algebra calculation and Stacks Tags 00GQ, 01S4, and 04DF.

The item has no sorry-free declaration in either Lean source checkout. I checked the target id and the relevant notions (`IsPurelyInseparable`, radicial, universal homeomorphism) throughout `WeilConjectures/`. The existing nodes `lem-weil-pbc-integral-injective-lying-over` and `lem-pc-integral-radicial-surjective-universal-homeomorphism` state exactly the surjectivity and final universal-homeomorphism facts used. The new child isolates the strictly smaller denominator/power assertion needed to identify residue-field extensions as purely inseparable; it is not a restatement of the target.

## Review by C1

I read the imported item and the parent `lem-weil-pbc-generic-finite-algebra-splitting` node. Step 1 uses the lying-over node only for its stated injective-integral hypothesis and surjectivity conclusion; finiteness gives integrality, and the fraction-field inclusion gives injectivity. Step 2 uses the new child for powers in the localized base and the existing purely inseparable-field node for the meaning of integral, universally injective, and surjective in the field case; passing the power relation to residue fields is the stated radicial criterion from Stacks 01S4. Step 3 uses the existing 04DF criterion exactly with the integral, radicial, and surjective properties established in the prior steps. I verified the hypotheses are the localized finite domain algebra from the item, and I recorded every cited statement verbatim in `citations.json`. I also ran the mandated Mathlib searches for both the item and the new child, including the unavailable LeanSearch results.

No statement was changed. The only correction to the imported empty proof was making the finite-integral, lying-over, residue-field, and universal-homeomorphism arguments explicit and introducing the smaller power-in-base child.

## Second reading by C1

- Item statement: checked the finite domain algebra setup and localization conclusion against the imported finite-algebra calculation and Stacks Tags 00GQ, 01S4, and 04DF; verdict: correct after making the localized rings explicit and correcting the source tags.
- Step 1: checked finiteness implies integrality and the injective fraction-field map, then applied the cited lying-over statement (Tag 00GQ); verdict: dependencies say exactly what is used.
- Step 2: checked residue-field representatives after localization, including the characteristic-zero equality case and the characteristic-$p$ power case; verdict: repaired, because an arbitrary positive power was insufficient and the radicial criterion is now cited from `def-weil-radicial-morphism` (Tag 01S4).
- Step 3: checked the integral, radicial, surjective hypotheses against the universal-homeomorphism criterion (Tag 04DF); verdict: correct.
- New node `lem-weil-pbc-power-in-base-after-localization`: checked self-contained hypotheses, definitions, explicit localization, and the two characteristic cases against the purely inseparable power calculation (Tag 0BR5); verdict: repaired from an arbitrary-power assertion to the required $p^n$ assertion (or equality in characteristic zero).
- Changes: replaced the child statement's arbitrary positive power by characteristic-sensitive $p^n$ powers; made both localization/base-change constructions explicit; replaced the field-specific radicial citation with the general radicial definition/equivalence; updated verbatim citations and Stacks source tags.

## Not duplicates

- `lem-weil-pbc-power-in-base-after-localization` vs `lem-weil-pbc-spread-purely-inseparable-factors`: the child is a ring-level localization and power calculation; the item concludes a radicial universal homeomorphism of spectra after an etale base change.
- `lem-weil-pbc-power-in-base-after-localization` vs `lem-pc-spec-pure-insep-integral-radicial-surjective`: the child concerns finite domain algebras over Noetherian domains and localized element powers; the existing node concerns the spectrum map of a purely inseparable field extension.
- `lem-weil-pbc-power-in-base-after-localization` vs `lem-pc-homeo-pure-insep`: the child supplies the finite-algebra spreading calculation; the existing node proves universal-homeomorphism behavior after arbitrary scheme base change along a field extension.
