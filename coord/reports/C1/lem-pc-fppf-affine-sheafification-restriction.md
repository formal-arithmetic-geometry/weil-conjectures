Files written:

- `lem-pc-fppf-affine-sheafification-restriction.json`: split statement.
- `dag/nodes/sec-picard-framework/lem-pc-fppf-affine-site-topos-equivalence.json`: new unsplit statement; Mathlib searches found no fppf-specific match.
- `citations.json`: verbatim citations for both proof steps.

Attachments: none.

WANTED: none.

The item had no matching declaration in `WeilConjectures/`; searches for its id, the Stacks tag 021V, and fppf sheafification terminology found no sorry-free declaration. The existing affine étale-topos node is a different topology and was not reused. The new node is strictly broader than the item: it states density and equivalence of sheaf categories, while the item derives a comparison of two sheafifications. Both proof steps use only the equivalence stated by the new node; the sheafification universal-property argument is written explicitly.

## Not duplicates

lem-pc-fppf-affine-site-topos-equivalence vs lem-pc-fppf-affine-sheafification-restriction: the new node states density of the affine inclusion and an equivalence of entire sheaf categories, while the item states only the induced canonical comparison between the sheafification of one presheaf and the restriction of its big-site sheafification.

## Review by C1

I read the item source, `literature/stacks-project/topologies.tex`, Tag 021V (Lemma 34.7.11), and checked that the item introduces a scheme $S$, a presheaf on the big fppf site, and the affine-site inclusion. I also read the existing `def-pc-fppf-site` and `def-pc-scheme` statements to verify the hypotheses and terminology. The new node uses the same Tag 021V source and states the density conditions and resulting equivalence needed by the item; its statement is self-contained and does not assume an unstated affine base.

Step 1 uses the new node's verbatim assertion that restriction along $u$ is an equivalence of sheaf categories, then applies the universal morphism from $F$ to its big-site sheafification. Step 2 uses the same assertion and spells out the universal-property uniqueness argument giving the comparison isomorphism and its functoriality. No additional non-elementary fact is hidden in a tag citation. I ran the required LeanFinder, Loogle, grep, and LeanSearch queries for the new node; LeanSearch was unavailable and is recorded as such. Small edge cases (empty presheaf and already-sheafified presheaf) reduce immediately to the same universal-property argument.

## Second reading by C1

- Item statement: checked against Stacks Tag 021V, Topologies Lemma 34.7.11 and `def-pc-scheme`/`def-pc-fppf-site`; hypotheses and comparison agree.
- New node `lem-pc-fppf-affine-site-topos-equivalence`: checked against Tag 021V label `lemma-affine-big-site-fppf`, including affine refinements, affine covers, and the induced topos equivalence.
- Step 1: the cited statement supplies the sheaf-category equivalence; restriction of the sheafification unit gives the displayed morphism.
- Step 2: checked against the equivalence, dense-subsite sheafification compatibility, and uniqueness in the sheafification adjunction; this yields the comparison isomorphism and functoriality.
- Mathlib searches: reran semantic, Loogle, and grep searches; semantic search found `CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility` at `Mathlib/CategoryTheory/Sites/DenseSubsite/Basic.lean:805`.
- Changes: corrected both source locations to name Tag 021V's actual lemma label and clarified the Step 2 source; no node was removed because the topoi-equivalence node is strictly broader than the item's comparison.
