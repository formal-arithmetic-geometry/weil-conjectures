# Stage-1 split: lem-sc-noetherian-open-closed-cohomology-sequence

## Files written

- dag/nodes/sec-curve-estimates/lem-sc-noetherian-open-closed-cohomology-sequence.json: split item; Mathlib search found no matching topological open-closed sequence.
- dag/nodes/sec-curve-estimates/lem-sc-topological-extension-by-zero-stalks.json: statement-only node, unsplit; Mathlib search found no matching topological extension-by-zero stalk theorem.
- citations.json: verbatim statement fragments for every proof citation.

## Attachments

None. No exact sorry-free declaration for the item or new topological stalk node was found in the read-only Lean source.

## Wanted

WANTED: the local literature/stacks-project/sheaves.tex, Lemma 00A5, for lem-sc-topological-extension-by-zero-stalks.
WANTED: the local literature/stacks-project/modules.tex, Lemma 02UT, for lem-sc-noetherian-open-closed-cohomology-sequence.
WANTED: the local literature/stacks-project/cohomology.tex, Proposition 02UZ and Lemma 02UV, for lem-sc-noetherian-open-closed-cohomology-sequence.

Those source files are absent from this read-only clone. I read the Stacks Project's official online pages for Tags 00A4, 00A5, 02UT, and 02UZ. The existing closed-pushforward cohomology node records 02UV and its previously reviewed proof. I did not download source files or write outside the sandbox.

## Issues found

The imported item had no proof. Its source entry placed Lemma 02UT under cohomology.tex, although 02UT is in Modules; the item proof now cites modules.tex at the exact-sequence steps and cohomology.tex at the closure and cohomology steps. The old Mathlib search entries were not supported by this worker's search log; the item now records only the searches I ran, including LeanSearch's unavailable result. Noetherianity is needed by the surrounding dimension induction, but neither the 02UT sequence nor its closure-support consequence uses it.

## Not duplicates

lem-sc-topological-extension-by-zero-stalks vs lem-sc-noetherian-open-closed-cohomology-sequence: the new node computes the stalks of extension by zero for every open inclusion; the item additionally proves the open-closed short exact sequence and the cohomology comparison for the closure.
lem-sc-topological-extension-by-zero-stalks vs lem-weil-pbc-module-extension-by-zero-adjunction: the latter concerns modules on an open subscheme and its scheme structure sheaf, while the new node concerns abelian sheaves on every topological space.
lem-sc-topological-extension-by-zero-stalks vs lem-weil-pbc-zariski-extension-by-zero-adjunction: the latter concerns the Zariski sites of a scheme and states the adjunction, not the two stalk formulas.
lem-sc-topological-extension-by-zero-stalks vs lem-weil-pbc-zariski-open-restriction-injectives: the latter concerns preservation of injectives under restriction between scheme Zariski sites.
lem-sc-topological-extension-by-zero-stalks vs lem-weil-pbc-sets-extension-by-empty-adjunction: the latter concerns sheaves of sets extended by the empty set, whose outside stalk is empty rather than the zero abelian group.

## Review by M1

I checked the item against Stacks 02UT's exact sequence and its stated proof by stalks, and against 02UZ's first proof paragraph, which identifies the first term with a direct image from the closure of the open. I checked the new node against 00A4's construction by sheafification and 00A5(3),(5)'s stalk and restriction formulas. The source documents are absent locally, so these checks used the official online pages; the missing files are recorded above.

Step 1 uses the new node's explicit inside-open stalk and adjunction-map clause and the existing closed-pushforward-stalk node's zero-off-closed clause. Step 2 uses the new node's zero-outside-open clause and the closed-pushforward node's on-closed germ isomorphism. In both steps the subspace restriction identifies the stalk of the restricted sheaf with the original stalk; the maps on germs are written in the steps, so the maps really are identities rather than merely abstract isomorphisms. Step 3 uses exactly the existing stalkwise short-exactness criterion, after the two point cases exhaust X.

Step 4 uses the new stalk formula to see that the sheaf vanishes off the closure, then the closed-pushforward stalk statement to compute both target stalk cases. I checked the restriction map on germs. The existing sheaf-of-sets stalk criterion says a map is an isomorphism exactly when all its stalk maps are; the inverse is additive because each open-section map is a bijective homomorphism. This generic criterion is declared as an off-unit tool use. Step 5 applies the existing 02UV node to the actual closed inclusion of the closure and its restricted abelian sheaf; those are exactly its hypotheses. I checked the empty-open case (the extension and its cohomology are zero), the all-open case (the exact sequence is 0 to F to F to 0), and a one-point closed complement. I corrected the missing proof, the source placement, and the unsupported search records. There is no unresolved mathematical step.

## Unfinished

None in the split. The new node is intentionally unsplit for its next worker.

## Second reading by M1

- Item statement: checked against the base DAG target and Stacks 02UT/02UZ; restored unchanged, with all hypotheses and the closure-support conclusion retained.
- Step 1: checked against 02UT and the cited extension-by-zero and closed-pushforward stalk statements; the open-point stalk maps are identities and the zero term is justified.
- Step 2: checked against 02UT and the cited stalk statements; the closed-point stalk map is the identity after the subspace germ identification.
- Step 3: checked against the existing stalkwise short-exactness criterion; the two point cases cover X.
- Step 4: checked against 02UZ and the closed-pushforward stalk formula; support outside the closure and the stalkwise isomorphism are stated explicitly.
- Step 5: checked against 02UV and the existing closed-immersion cohomology comparison; its hypotheses apply to the closure inclusion and restricted sheaf.
- New node `lem-sc-topological-extension-by-zero-stalks`: checked against Definition 00A4 and Lemma 00A5, parts (2), (3), and (5); self-contained statement, TeX, dependencies, and recorded searches are present.

Changes made: restored the item statement and statement dependencies from the base DAG because target statements are fixed; retained the five-step proof and its citations; recorded the source correction and second-reading verdicts here. The source files are absent locally, so the checks used the official Stacks pages for Tags 00A4, 00A5, 02UT, 02UV, and 02UZ.
