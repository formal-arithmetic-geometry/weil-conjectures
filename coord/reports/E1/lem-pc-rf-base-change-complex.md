1. Files written

- `dag/nodes/sec-picard-framework/lem-pc-rf-base-change-complex.json`: repaired proof.
- `dag/nodes/sec-picard-framework/lem-pc-rf-base-change-single-complex-criterion.json`: statement-only unsplit node; Mathlib no match.
- `dag/nodes/sec-picard-framework/lem-pc-derived-pullback-tor-independent-flat-complex.json`: statement-only unsplit node; Mathlib no match.
- `citations.json`: verbatim citations for all uses.

2. Attachments

None. No sorry-free declaration states the item.

3. WANTED:

None.

4. What was wrong or changed

The returned version incorrectly used a separated single-module theorem, a K-flat lemma requiring flatness over O_X, and an ill-typed abstract truncation principle. I deleted the truncation node and replaced the proof with the Stacks Tags 0A1B, 0A1C, and 0A1E single-complex criterion. The new stalkwise node supplies the required tor-independence for terms flat over S, including the arbitrary E factor and qcqs f.

## Review by E1

I read the complete item and neighboring source metadata, then checked the new criterion against the Tag 0A1D route. Step 1 uses exactly the new criterion's conclusion and matches its qcqs, bounded-above, quasi-coherent, and arbitrary-D_QCoh hypotheses. Step 2 uses exactly the new tor-independence statement; its stalk formulation identifies the local derived tensor, and the cited `lem-pc-stalk-tensor-complex` states the tensor/stalk isomorphism verbatim. Step 3 is the direct substitution of the quasi-isomorphism into the criterion. I removed every citation to the returned module and truncation nodes, checked that no deleted node remains cited, ran the required Mathlib searches for both new nodes, and verified each quote in `citations.json` is copied from its node statement.

## Not duplicates

`lem-pc-rf-base-change-single-complex-criterion` vs `lem-pc-rf-base-change-complex`: the new node is a conditional criterion assuming tor-independence of G; the item proves that condition from S-flatness and states the resulting comparison.

`lem-pc-derived-pullback-tor-independent-flat-complex` vs `lem-pc-flat-complex-derived-pullback`: the new node concerns pullback along `g':X_T -> X` of a complex flat over the base S and gives stalkwise tor-independence; the existing node concerns a complex of flat O_S-modules along `g:T -> S`.

`lem-pc-derived-pullback-tor-independent-flat-complex` vs `lem-pc-rf-base-change-complex`: the new node is the auxiliary stalkwise tor-independence condition for G alone; the item includes arbitrary E and the derived direct-image comparison.

5. Could not finish

No unresolved issue remains before the dry run.

## Second reading by E1

- Item statement: checked against Stacks `perfect.tex`, `lemma-base-change-tensor` (Tag 0A1D); qcqs, arbitrary `E`, bounded-above `S`-flat `G`, and the precise derived comparison agree, including zero and identity-base-change cases.
- Step 1: checked against `lemma-single-complex-base-change` (Tag 0A1C) and `lemma-single-complex-base-change-condition` (Tag 0A1B); repaired to use the actual stalkwise condition rather than global quasi-isomorphism alone.
- Step 2: checked against the stalk calculation in Tag 0A1D and the tensor/stalk identification; agrees after making the displayed stalk comparison the conclusion.
- Step 3: checked as substitution of the verified condition into Tag 0A1C; elementary.
- `lem-pc-rf-base-change-single-complex-criterion`: statement-only, self-contained with scheme, cartesian square, derived-category, pullback, direct-image, and stalk data; source labels Tags 0A1B and 0A1C; Mathlib searches recorded; the `G=O_X` non-Tor-independent-base-change case exposed and repaired the overstrong formulation.
- `lem-pc-derived-pullback-tor-independent-flat-complex`: statement-only, self-contained with the flatness hypothesis and explicit stalk map; source Tag 0A1D; Mathlib searches recorded; tested on the zero complex and identity base change.
- `lem-pc-rf-base-change-complex`: item node has proof steps and source/blueprint metadata; no duplicate or Mathlib declaration found.

Changes made: replaced the false criterion “global derived-pullback map is a quasi-isomorphism” with the source’s stalkwise base-change condition; changed the flat-complex node to prove that condition; updated steps and verbatim citations.
