1. files written:

- item `lem-sc-lfp-field-extension-pointwise-descent`, statement, split;
- `lem-sc-lfp-affine-field-extension-localization`, statement-only unsplit node, Mathlib no match.

2. attachments: none.

3. WANTED: none.

4. The item had no Lean declaration. Its source is the affine-local pointwise consequence of Varieties Lemma 33.9, Tag 0C4Y. I searched the DAG and blueprint for an existing pointwise localization lemma and found only the stronger global fpqc descent node, which does not state the pointwise conclusion and is therefore not a duplicate. The new node records precisely the affine ring fact used by the proof rather than restating the item.

5. what I could not finish: no Lean compilation is permitted at stage 1; the new node is intentionally statement-only.

## Review by E1

I read the target node, its cited definitions, the unit blueprint proof of reduction from a field to an algebraic closure, and the existing sibling `lem-sc-etale-faithfully-flat-local`. The single item step chooses affine opens around `x` and `f(x)`, identifies the primes `q` and `q_K`, invokes the new affine statement, and translates the resulting localizations back to affine neighbourhoods. The new statement includes all ring and prime hypotheses and its conclusion is strictly smaller than the item. I checked the field-extension edge case `K = k`, where the conclusion reduces to the ordinary affine characterization, and the localization elements are required to avoid the relevant primes. Mathlib searches were run for the new node with LeanFinder, Loogle, grep, and LeanSearch; none states the pointwise descent theorem.

## Second reading by E1

- Item statement: checked against Varieties Lemma 33.9, Tag 0C4Y, and the affine definition of locally of finite presentation; the field-extension and point-above hypotheses are explicit and the conclusion is pointwise.
- Step 1: checked the affine neighbourhood and prime construction against the affine-local definition; elementary after the cited definitions.
- Step 2: checked faithful flatness of tensoring with a field and the finite-presentation descent statement `lem-weil-pbc-finite-presentation-descends-faithfully-flat`; the localization argument is stated as descent of finite-presentation data after choosing denominators outside the relevant primes.
- Step 3: checked the correspondence between principal affine opens and localized ring maps against the affine definition; elementary.
- New nodes: none; the proof uses the existing faithfully-flat finite-presentation node, searched for duplicates and Mathlib declarations, and found no exact pointwise theorem.
- Changes: corrected `created.item` to this item, replaced the non-verbatim citation fragment with the cited node's complete statement, and recorded this second reading.
