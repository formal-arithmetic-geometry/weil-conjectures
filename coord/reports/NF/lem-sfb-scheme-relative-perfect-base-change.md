# NF stage-1 delivery: lem-sfb-scheme-relative-perfect-base-change

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-relative-perfect-base-change.json: existing statement, split into five affine-model steps; no Mathlib match for the item.
- citations.json: full verbatim statements for all 26 proof citations (including repeated uses).
- report.md and searches.jsonl: review and actual searches. write_split.py is a sandbox-only preparation script.

No new nodes; no new Mathlib leaves. The statement and its statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and relativePerfect/relativelyPerfect notions and for pseudo-coherent pullback terminology. No declaration supplies the whole item. Existing sorry-bearing pseudo-coherent infrastructure is not claimed as finished.

## WANTED

None. All mathematical sources needed for this proof are present in literature/stacks-project.

## What changed and what was wrong

The item was an unsplit statement-only prerequisite of coherent relative-dualizing-pair base change. I expanded the first proof of perfect.tex Tag 0DI5. The algebra proof uses the base-change comparison and pullback of Tor amplitude; here those are expanded using the existing K-flat tensor comparison and bounded flat model nodes. The crucial distinction is that A is R-flat whereas R-prime need not be R-flat. I did not use the false assertion that the stalk ring of a fibre product equals the tensor product of the two stalk rings: all tensor calculations occur on affine fibre-product charts.

Source-tag audit corrected draft references: the affine relative-perfect criterion is 0DI2 (not 0DI1, which is an example); the algebra relative-perfect base-change lemma is 0DHW (not 0DI4, which is the scheme perfect-implies-relative-perfect lemma). The existing affine pullback node calls 08DW "lemma-pullback"; the actual label in this snapshot is lemma-quasi-coherence-pullback, and the step uses that correct label. These are draft citation corrections, not a statement dispute.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor reports None. Its precise inherited from.place and via chain are retained. I read the current latest chapter and sk-thm-sf-ctf-stability unit and its direct-images proof (3). The current text no longer spells out this coherent-duality support branch; I retained the assigned prerequisite and its route rather than editing the chapter/unit or its historical ancestry. Searches of the whole imported blueprint for "relative perfect", "relative perfection", "relative Tor", "pseudo-coherent pullback", "Tor independence", and "0DI5" found no equivalent blueprint statement. The only relative-Tor keyword hit is the divisor class lemma, not this assertion.

## Unfinished work

None within this one-level split. All non-elementary inputs already have nodes; these dependencies may independently remain open. This delivery neither writes Lean nor claims their proofs finished.

## Not duplicates

No new nodes. The existing space relative-perfect base-change theorem uses small etale structure sheaves and algebraic spaces; invoking it directly would require a site-comparison argument. I instead used the existing Zariski affine lemmas, avoiding a new scheme or ring restatement of either clause of the item. The existing space Tor-amplitude theorem was likewise not silently specialized across coefficient sites.

## Review by NF

I read perfect.tex definition-relatively-perfect (0DI0), lemma-affine-locally-rel-perfect (0DI2), lemma-base-change-relatively-perfect (0DI5), lemma-affine-compare-bounded (06Z0), lemma-pseudo-coherent-affine (08E7), and lemma-tor-dimension-rel-affine (0DHY). I read more-algebra.tex lemma-base-change-relatively-perfect (0DHW), lemma-pull-tor-amplitude (066L), lemma-tor-amplitude (0654), lemma-derived-tor-quasi-isomorphism (064K), and the K-flat-derived-tensor construction and lemma-derived-tor-quasi-isomorphism-other-side. I read algebra.tex lemma-flat-base-change (00HI) and lemma-flat-localization (00HT), especially clause (6). No new node requires a separate source.

Step 1 uses the affine-open-basis statement to choose each neighbourhood, the open-fibre-product statement for the actual open containing x-prime, and the affine-spectra fibre-product statement for A-prime = A tensor_R R-prime. The pseudo-coherent definition supplies the retained local models. The ringed Tor stalk test applies to the inverse-image base structure sheaf as a ringed-space ring sheaf, and identifies the same stalk rings on restrictions. Thus there is no assumption that an arbitrary intersection of affine opens is affine.

Step 2 uses the two stalk-localization statements to identify the map R_p to A_q, then the flat-morphism definition gives precisely the flatness assumed by affine-sections-flat-over-base with M=A. The pseudo-coherent-qcoh statement supplies the domain hypothesis for the affine derived equivalence. The affine pseudo-coherent criterion gives exactly a bounded-above finite-free A-model, not a bounded model. The relative affine Tor criterion, which I opened and read in full, has the required locally-finite-to-finite clause on affine U. Its proof uses quasi-compactness only of U, never of X; the interval may vary from chart to chart.

Step 3 applies bounded-above-flat-K-flat over both A and R. The reason finite free terms remain R-flat is written out as finite direct sums of exact tensor functors; this is an elementary finite-sum calculation, not a new node. The affine K-flat pullback chart statement applies to the chosen Q because it is A-K-flat; it does not falsely provide a representative on its own. The representative already came from step 2. The finite-free base-change calculation is written degreewise, and the affine pseudo-coherent criterion then says exactly what is needed. No flatness of the base-changing map is invoked.

Step 4 uses base-tensor-ordinary-iso with B=R-prime and E=A-prime, preserving the explicit R-prime-module structure. The flat-model equivalence is first applied to the restricted R-complex to produce F supported in the already chosen interval. Both Q and F are R-K-flat by the bounded-flat lemma. The derived-tensor-second-factor-functor statement explicitly supplies a functor D(R) to D(R-prime), with its computation on every K-flat resolution, so applying it to the isomorphism of models is justified; I am not identifying two complexes merely because their individual cohomology groups agree. The flat-module-base-change node then applies to each R-flat F^i for arbitrary R to R-prime. Its statement has no flatness hypothesis on that map. The reverse flat-model criterion gives the Tor interval of the R-prime-complex underlying Q-prime. This is the actual argument behind preservation of amplitude, not an uncited invocation of that clause as a new lemma.

Step 5 uses the same affine relative-Tor criterion in its fixed-interval form over R-prime to A-prime. The derived-pullback composition statement identifies restriction of the global pullback with the calculated affine pullback. The definition's tensor formula for an open immersion reduces to ordinary restriction; the base-ring stalks on V-prime and S-prime agree. The ringed stalk test therefore supplies the relative interval over the correct ring (f-prime)^{-1} O_{S-prime}. The pseudo-coherent definition finishes by local finite-free models. This does not infer Zariski locality from an etale theorem without comparison.

I tested the proof on E=0, empty X or X-prime, identity base change, nonflat base change Z to Z/2 with A=Z[t], and non-Noetherian flat algebras. The finite-free model may be unbounded to the left; bounded-above K-flatness is sufficient, and only the auxiliary R-flat model is bounded. On an infinite disjoint union, the intervals can vary and no uniform global bound was introduced. In the nonflat example termwise tensor is justified by K-flatness, not by tensoring an arbitrary quasi-isomorphism with Z/2. No new statement introduces an untested hypothesis.

I checked delivery-errors B through E: no new definition, duplicate, restated clause, or unsplit-node proof is being created; all existing cited node statements were opened, and citations.json copies those statements verbatim. Generic off-unit tools are declared in split_report.tool_uses with their purposes. Proof dependency union agrees with uses. All five steps are below 2000 characters and none hides a separate comparison lemma: the required comparison and flat-model results are already cited. No SGA source is used. Mathlib searches were run through msearch.py in both semantic phrasings plus Loogle, LeanSearch and grep; their records are retained. The hits are ordinary scheme flatness/base-change, exact scalar extension and truncation, not this theorem; Module.Flat.isBaseChange and its baseChange instance were read in Flat/Stability.lean and are already represented by the cited flat-module-base-change node.

## Validation

The server review_split check passed with zero new nodes and the declared generic tool uses. Full dry-run and final push results are recorded below when completed.
