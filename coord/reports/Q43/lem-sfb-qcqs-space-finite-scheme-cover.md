# Q43: lem-sfb-qcqs-space-finite-scheme-cover

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-qcqs-space-finite-scheme-cover.json: existing statement, now split into four steps; not a Mathlib leaf.
- citations.json: five verbatim statement quotations, one for each cited node in its step.
- searches.jsonl: six actual msearch.py searches made for this item. Their tool outputs were read; the earlier Q06 search records in the item are retained.
- report.md: this report.

There are zero new nodes and zero new Mathlib leaves. The statement, statement dependencies, source, creation record, inherited blueprint ancestry and all other maintainer fields are retained.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint tag and for finite surjective scheme covers found no project declaration stating the arbitrary-base algebraic-space result. Scheme finite-surjective-image affineness results and scheme-cover results do not state this item.

## WANTED

None. All sources needed for the split are present locally.

## Problems found and corrections

The item had no proof. I supplied the proof of Stacks 09YC(1), using existing nodes for its three substantive inputs. I did not add Noetherian, separatedness, field, or finite-type-over-the-base hypotheses. The finite-presentation assertion comes from 09YA, not from the false assertion that every finite morphism is finitely presented. The passage from a slice limit over X to a limit over S is written out, and surjectivity of the selected stage is proved from the factorization rather than assumed for the limit projection.

The current latest blueprint was read at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md, together with the recorded unit and chapter. This item is a supporting prerequisite several levels below the unit, so no unit or chapter route is replaced. Its inherited blueprint.from.node is null, exactly as blueprint_refs.py ancestor reports; I have not invented an ancestor or altered maintainer-owned ancestry. The inherited from.place already identifies the adequate Serre criterion and Alper Theorem 4.3.1 final paragraph. Whole-blueprint searches for 09YC, finite scheme, finite cover and scheme cover give no same-statement blueprint node.

## Unfinished work

No mathematical part of this item's one-level split remains. Existing prerequisite nodes retain their own stage responsibilities. No Lean was written and no compiler or build tool was run.

## Not duplicates

No new-node pairs exist. In particular, I reused lem-sfb-qcqs-space-integral-scheme-cover (09YB), lem-sfb-integral-space-finite-presentation-limit (09YA), and lem-sfb-affine-space-limit-schematic-stage (07SR), instead of creating aliases. The existing lem-sfb-noetherian-space-finite-scheme-cover has the additional hypotheses of a separated Noetherian space over a field and lacks the finite-presentation conclusion; it does not state this arbitrary-base item. I inspected its statement and proof as a nearby comparison, but do not cite it or use its stronger hypotheses.

## Review by Q43

I read spaces-limits.tex, Tag 09YC (proposition-there-is-a-scheme-finite-over), statement and proof at lines 3569 onward. Clause (1) is exactly the item, including finite presentation and an arbitrary scheme base. Its proof takes an integral scheme cover, writes it as a limit of finite finitely presented spaces, and selects a scheme stage. The extra descent-of-opens and morphisms in the source is needed for its atlas-factorization clause (2), which this item does not assert, so it is not used here. I also read decent-spaces.tex Tag 09YB (lemma-there-is-a-scheme-integral-over) at lines 1807 onward, spaces-limits.tex Tag 09YA (lemma-integral-limit-finite-and-finite-presentation) at lines 2722 onward, and Tag 07SR (lemma-limit-is-scheme) at lines 1218 onward. There are no new nodes requiring separate source review.

For step 1 I opened lem-a1-space-etale-open-image and checked its last sentence: the existence of a surjective etale map from a quasi-compact scheme is equivalent to topological quasi-compactness. This handles exactly the difference between the item's atlas formulation and the two prerequisite statements' topological formulation. The given absolute diagonal assumption already supplies their quasi-separatedness condition. The source of this criterion is spaces-properties.tex Tag 03E4, not any assertion about a Noetherian base.

For step 2 I opened lem-sfb-qcqs-space-integral-scheme-cover: its statement explicitly gives an S-scheme and a surjective integral S-map for every qcqs algebraic space over S. All hypotheses have been established in step 1. It does not give finiteness or finite presentation, and this step does not take either from it.

For step 3 I opened lem-sfb-integral-space-finite-presentation-limit: its statement explicitly supplies a small nonempty directed set, qcqs stages, affine transitions, finite finitely presented structure maps, compatible projections and a limit over X. The integral-map and qcqs-target hypotheses hold. The conversion to a limit over S uses only the universal property just quoted: any compatible family has one map to X by directedness, and uniqueness uses a single index. This elementary argument is included in the step, not hidden in a new node.

For step 4 I opened lem-sfb-affine-space-limit-schematic-stage: its statement requires a small nonempty directed system of qcqs spaces over S, affine transitions, and a scheme limit over S, and gives a scheme stage. Step 3 supplies every system hypothesis, and step 2 supplies the scheme limit. Its finite finitely presented structure map was already supplied by step 3. I opened def-a1-space-point-topology for the field-valued point-image definition: the image of any lifted point under the projection is a point class in the chosen stage, and the composite is q. Thus the structure map is surjective without any surjectivity hypothesis on the projections. Every step's cited statement has an exact supporting quote in citations.json.

I tested the proof on X empty (the argument remains valid and the surjectivity clause is vacuous), on X a scheme, and on non-Noetherian affine bases. None of the three inputs needs separatedness of X, Noetherianness, or a field. I checked the B--E return categories: no new unsplit statements, proof sketches in statements, missing definition dependencies, false tag identifications, clause-restatement nodes, off-route replacements, or inline non-elementary comparison lemmas were introduced. The three substantive geometric facts are existing cited nodes; the only remaining calculations are the displayed universal-property and point-factorization arguments. All steps have fewer than 2000 characters.

For the Mathlib check I ran leanfinder, loogle, grep and leansearch through msearch.py, then a second natural-language phrasing and a broader grep. I read all returned hits and inspected Mathlib/AlgebraicGeometry/Morphisms/Descent.lean:48 and Cover/QuasiCompact.lean:140. The former assumes a scheme target and a source-local morphism property; the latter turns a finite family of quasi-compact covering maps into a covering predicate. Neither gives a finite finitely presented scheme cover of an algebraic space. The algebraic-space grep returned no hit. Thus the item remains split rather than being falsely marked a Mathlib leaf.
