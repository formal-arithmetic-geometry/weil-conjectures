# Q37: lem-sfb-proper-dc-preserves-integral

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-dc-preserves-integral.json`: statement; split into six steps, using existing nodes only. Mathlib verdict: no match after two semantic phrasings, LeanSearch, Loogle and logged source grep.
- `citations.json`: nine step/node entries, with verbatim portions of the cited statements.
- `report.md`: this report. No new nodes and no Mathlib leaves.

The sandbox also retains `searches.jsonl`, the extracted Bhatt–Scholze text and the item-specific writing script; these are working records, not additional DAG nodes. The repository and all Lean sources were read only. No compiler, Lake, build or agent was started.

## Attachments

None. I searched `lean/WeilConjectures/` by the item tag, full upstream declaration and the proper bounded-constructible notion, and inspected `ProperLowerStarEllAdic.lean`. The integral declaration is lines 93–101 and ends in `sorry`. The continuous and algebraic-closure variants also end in `sorry`; their uses in `UpperShriekLocalizing.lean` are not independent proofs. The Sheaf wrapper found by the search does not provide a completed integral proof.

## WANTED

None. The blueprint, upstream Lean reference and Bhatt–Scholze paper are available locally.

## Scope discrepancy and correction

STATEMENT-DISPUTED: the imported reference to `sk-def-sfb-dc-setting` after “a field k in which ell is invertible” is incompatible with the actual scope of this upstream declaration. That definition requires positive characteristic and separated finite-type schemes over the field. The upstream declaration requires only a field with characteristic different from ell, a structure morphism of a Noetherian target to it, and a proper map. For example, `k = Q`, `Y = Z = Spec Q`, and `p = id` meet the upstream hypotheses and the explicit words of the imported item, but cannot satisfy the positive-characteristic convention of that cited definition. No counterexample to the proper-finiteness claim is asserted.

I removed that reference and its statement edge, preserving the explicit prime, field, coefficient, Noetherian and proper hypotheses. I expanded “Noetherian” to its quasi-compact and locally Noetherian meaning and cited the existing proper-morphism definition. This is a scope repair to the source's intent, not a new finiteness hypothesis. `blueprint.same_as` is now empty: `det-thm-sfb-proper-base-change-integral` contains a corresponding clause only under standing-scheme assumptions and also asserts other clauses, so its complete statement is not equal to this item. The original blueprint ancestor is retained and its precise place filled. The ancestor utility reports no computed ancestor for this maintainer-created item because `created.item` is null; no new node needs an ancestor synthesized from that broken creation chain.

The statement is not the key statement of the open-immersion unit, and I have not changed the unit or chapter. The unit explicitly invokes proper finiteness; this item realizes that proper integral input. I did not use the open-immersion conclusion as a premise.

## Unfinished work

None at this split level. Existing dependency proofs remain their own items. This delivery creates no replacement of the whole item or of one of its clauses.

## Not duplicates

No new node is proposed. The whole DAG and blueprint were searched for proper direct image and heart-amplitude inputs, and the already present Noetherian proper cohomology, uniform heart bound, finite devissage and total/plus compatibility nodes were reused. The standing-scheme integral proper theorem is narrower in hypotheses; I did not apply it to this general Noetherian base. No duplicate-tag pair is introduced.

## Review by Q37

I read the item's chapter and open-immersion unit, the current blueprint's lower-star assertion and integral proper-base-change proof paragraph (1), the upstream integral declaration with its field and scalar-tower parameters, and Bhatt–Scholze Theorem 6.7.1, Lemma 6.7.2 and Remark 6.8.15. The proper alternative of 6.7.1–6.7.2 does not impose the quasi-excellence required in their other alternative. Their integral proof proceeds through completeness, residue reduction, the étale comparison and finite proper finiteness. Those geometric ingredients are already represented by the existing Noetherian proper input nodes used here. This delivery packages their separate heart amplitude and per-degree constructibility conclusions into bounded constructibility. It is marked as an agent proof because this packaging is not a verbatim proof in the paper. No new node has a source to audit.

For step 1 I read `sk-def-sfb-bounded-constructible`: it states both a finite cohomological interval and constructibility of every cohomology module. I retained its general stratified local-finite-presentation predicate, including arbitrary local presentation matrices and torsion modules. I read `sk-def-sfb-condensed-ring`: the coefficient is the continuous induced integer ring of the given embedded finite extension. The coefficient certification needed by the two proper inputs is immediate from their listed induced-integer-ring case. I also read the actual integral constructor in `WeilConjectures/CategoryTheory/RingObjects/Condensed/FinitenessCoefficient.lean` lines 85–88: its prime, embedding, scalar tower and finite-dimensional hypotheses are precisely the data of the item; it is not a further mathematical finiteness theorem. Step 1 is elementary unpacking of these notions.

For step 2 I read the statement of `sk-def-sfb-module-derived-pushpull` and the full statement of `src-right-derived-functor-plus-compatibility`, then inspected the corresponding upstream compatibility declaration. The former gives the actual total derived functor of the full additive module composite and its bounded-below version into D-plus. The latter identifies that bounded-below version after inclusion with the total functor. Its additive/enough-injectives/K-injective structures are the ones used in constructing those module-derived functors. Therefore the actual total image is bounded below. I deliberately assert only existence of some lower bound c; I do not use an unstated exact value or replace total pushforward by a different derived abelian-sheaf functor. The relevant classical bounded-below construction was checked in Stacks `derived.tex`, Tag 05TI, `lemma-enough-injectives-right-derived`; no extra non-elementary step from that source is silently imported.

For step 3 I opened `lem-sfb-noetherian-proper-heart-uniform-bound` and read its statement, not only its sketch. It explicitly allows characteristic zero and no finite-type/separatedness condition on the target's structure map. It states one integer d for all heart objects of the replete Serre-and-coproduct closure. Applying its integral coefficient case is legitimate for this E. Each cohomology of K is in that class because the class contains every constructible module. Its conclusion is a heart upper bound only; step 3 does not pretend it already proves the item's bounded-image conclusion.

For step 4 I read `lem-pc-right-derived-functor-triangulated` and its source instances for the K-injective right derived functor, and `lem-sfb-bounded-heart-amplitude-devissage` including its finite-truncation proof. The former gives both triangle preservation and integer-shift compatibility for F; the latter requires bounded K, a replete class containing zero, all cohomologies in the class, and the uniform heart bound. These are exactly step 1 and step 3. Its conclusion is the upper bound b+d, with the cohomological shift convention as stated. I also read the bounded-below paragraph of the blueprint's proper-window proof. No unbounded convergence, Milnor argument or implicit uniformity assumption is inserted at this step.

For step 5 I opened `lem-sfb-noetherian-proper-constructible-cohomology`: it explicitly gives constructibility of every H^q of the actual total image for bounded constructible input, with the same broad Noetherian proper hypotheses and the induced integer coefficient case. Its explicit predicate is stratified local finite presentation. I do not silently substitute the smaller finite constant-model predicate, require a derived-completeness assumption, or infer any cohomological bound from that node. The two independent bounds have already been established.

For step 6 I compared the assembled conclusion with the two clauses in `sk-def-sfb-bounded-constructible`. Below c and above b+d there is vanishing, so the interval with upper endpoint max(c,b+d) is ordered even if the two bounds cross. Every cohomology is constructible by step 5. This is an elementary application of the definition, with no new lemma hidden in “hence”.

I checked the C1/C4 requirements by reading every cited statement and wrote its exact used substring into `citations.json`; the nine quotes were checked locally as literal substrings. The item is not merely moved into another node: two distinct existing geometric inputs give different pieces, and the finite devissage and total/plus comparison carry the actual combination. I traversed statement and proof dependencies of the five generic theorem inputs: none reaches the item, so these uses create no cycle. The generic off-unit inputs are explained individually in `split_report.tool_uses`; no maintainer-owned `tool_uses` field was written.

Small cases checked were the zero complex, empty source, identity of Spec Q, finite identity maps with torsion integral cohomology, arbitrary negative shifts, and crossing lower/upper bounds. None requires an added positivity, torsion-freeness, finite-dimensional-base or finite-type-over-k assumption. No new statement needs a separate small-case test. Every proof step is shorter than 2000 characters; there is no concealed long-step lemma.

For the remaining B–E checks: there are no new statement-only nodes to carry accidental proofs, no Mathlib leaf with an unverified signature, no elementary or duplicate helper introduced, and no circular application of the broader lower-star assertion. All new recorded searches are exactly those in `searches.jsonl` with the actual returned results; both semantic phrasings produced only unrelated general constructions, underived functors or constructible subsets, while Loogle and the coefficient-specific grep found no match. The inherited maintainer searches were preserved. I inspected the returned Mathlib source declarations for module pushforward and condensed-object construction; neither supplies integral proper derived finiteness. The only change of statement scope is explicitly explained above. The required dry run and delivery are the next validation steps.
