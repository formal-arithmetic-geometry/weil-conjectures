Files written:

- `dag/nodes/sec-picard-framework/lem-sc-proper-flat-right-adjoint-open-support.json` (statement, split)
- `lem-sc-proper-flat-pseudo-coherent-direct-image` (statement, Mathlib no match)
- `lem-sc-perfect-support-map-lift` (statement, Mathlib no match)
- `lem-sc-pseudo-coherent-support-annihilation` (statement, Mathlib no match)

Attachments:

None. No sorry-free declaration with the item tag or exact statement exists in either Lean source checkout.

WANTED:

None.

What was checked and corrected:

The item and the three children were checked against `literature/stacks-project/duality.tex`. The item is Lemma 48.4.4, case (1), whose proof first detects a non-supported right-adjoint object by a perfect test map, then lifts that map from the open, uses pseudo-coherence of the proper flat pushforward, applies the support-annihilation lemma, and obtains a contradiction through the projection/base-change formula. The three new nodes are precisely the non-elementary inputs named in that proof: Tags 09IM, 0CSD, and 0A9C. Step 1 cites the existing perfect-generation statement and the new lifting statement; the hypotheses that X is quasi-compact and quasi-separated come from the item's scheme conventions. Step 2 is the adjunction definition of the derived direct image. Step 3 cites the exact pseudo-coherence and annihilation statements, with M instantiated as Rf_*P and Q as the given supported object. Step 4 cites the existing derived projection formula and uses adjunction to transfer vanishing. Step 5 is the elementary restriction contradiction because I is an isomorphism on V. The small edge cases checked were V=Y (support condition is vacuous) and V empty (the conclusion says a(Q) is supported on all of X). Mathlib searches were run for the item and every new node with LeanFinder, Loogle, grep, and LeanSearch; no matching Mathlib theorem was found, and LeanSearch was recorded as unavailable.

## Review by K1

I read the complete Stacks proof at `duality.tex` around Lemma 48.4.4 and checked every cited DAG statement verbatim. The perfect-generation node supplies the nonzero test map, the lift node supplies a global perfect source preserving nonzeroness on U, the proper-flat pseudo-coherence node supplies pseudo-coherence of Rf_*P, and the annihilation node supplies I -> O_Y with the required support and vanishing composite. The projection-formula node states exactly the tensor/direct-image isomorphism used in Step 4. The hypotheses proper, flat, finite presentation, qcqs, quasi-compact V, and Q in D_QCoh^+ are all the item's hypotheses and are used where the Stacks proof uses them. I corrected the initial empty proof by adding these five steps, adding the three missing non-elementary children, and recording exact citation quotes in `citations.json`.

What could not be finished: no Lean proof was written, as required for stage 1; the three new children remain unsplit statement nodes.

## Second reading by K1

- Item statement: checked against Stacks `duality.tex`, Lemma `lemma-proper-flat-relative` (Tag `0E4G`), clause (1); corrected the unjustified `D_QCoh^+` restriction to all `D_QCoh` objects supported on the closed complement of a quasi-compact open.
- Step 1: checked against the perfect-generation argument in `duality.tex` and the support-preserving lift lemma `perfect.tex`, Tag `09IM`; verified the cited statements supply a nonzero open map and a global supported perfect lift.
- Step 2: checked against the definition of the right adjoint and the adjunction used in `duality.tex`; the cited direct-image node supplies the functor and this is elementary adjunction transposition.
- Step 3: checked against `perfect.tex`, Tags `0CSD` and `0A9C`; corrected the annihilation child to include the perfect-source alternative, so no bounded-below hypothesis is silently imposed on the item.
- Step 4: checked against the derived projection formula node and the adjunction; the tensor/direct-image identification and vanishing transfer are exactly what the cited statements provide.
- Step 5: checked on restriction to `U`, where `I -> O_Y` is an isomorphism; the resulting map is the original nonzero map, giving the contradiction.
- `lem-sc-perfect-support-map-lift`: statement checked against the source lemma, including closed support, direct-summand restriction, and compatibility of the lifted map; Mathlib searches recorded and no match found.
- `lem-sc-proper-flat-pseudo-coherent-direct-image`: statement checked against `perfect.tex`, Tag `0CSD`; hypotheses proper, flat, finite presentation, and pseudo-coherence agree; Mathlib searches recorded and no match found.
- `lem-sc-pseudo-coherent-support-annihilation`: statement checked against `perfect.tex`, Tag `0A9C`; both source alternatives and the open isomorphism were restored; Mathlib searches recorded and no match found.
- Edge cases checked: `V=Y` makes the support condition empty and the conclusion vacuous; `V=empty` makes the conclusion support on all of `X`; identity and empty schemes satisfy the statement without adding hypotheses.

Changes: fixed the item's stale `created.item`; broadened the item from bounded-below objects to all supported `D_QCoh` objects; repaired the lift and annihilation child statements to match the source; updated verbatim citation quotes accordingly.
