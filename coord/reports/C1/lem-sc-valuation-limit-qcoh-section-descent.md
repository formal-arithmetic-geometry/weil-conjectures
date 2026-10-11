1. Files written:

- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-limit-qcoh-section-descent.json`: statement, kind statement, no Mathlib match; split into four proof steps.
- `dag/nodes/sec-abelian-varieties/lem-sc-valuation-limit-affine-pushforward-colimit.json`: statement-only supporting node, no Mathlib match.
- `citations.json`: verbatim citations for every proof-step dependency.

2. Attachments: none.

3. WANTED: none.

4. The imported item had no proof. The source proof of Limits Lemma 01Z0 uses the relative-spectrum construction and the tensor description of pushforward modules; those are not stated by the existing affine-limit node, so I created the strictly smaller supporting node rather than hiding that argument in an elementary step. The item then uses the existing qcqs filtered-colimit-of-quasi-coherent-modules section lemma and the existing filtered-colimit elementwise zero criterion. No statement was weakened or changed.

## Review by C1

I read the item against `literature/stacks-project/limits.tex`, Limits Lemma 01Z0 (`lemma-descend-section`), including its hypotheses in Situation `descent` and the displayed chain of equalities in the proof. I also read the source passage for the new affine pushforward/tensor-colimit node: the first two paragraphs of the same lemma construct the limit as `Spec_{S_0}(colim A_i)`, identify the pushforwards with `F_0 tensor A_i`, and use tensor commuting with directed colimits. The item keeps the original hypotheses: a directed inverse system of qcqs schemes with affine transitions, a chosen stage, and a quasi-coherent module pulled back from that stage.

Step 1 uses the statement of `lem-weil-pbc-limit-affine-transition`, which supplies the affine projections and the restricted limit system; the cofinal-tail reduction is elementary once that statement is available. Step 2 uses the new node exactly for the relative spectrum, pushforward/tensor identities, and colimit identification; its statement says all three facts explicitly. Step 3 uses `lem-weil-pbc-quasi-coherent-module-colimit-affine-sections`, whose statement gives bijectivity of sections on an affine open for a directed colimit of quasi-coherent modules; `X_i` is qcqs, so its global space is covered by the cited theorem's affine-local argument. Step 4 uses the new node's pushforward identities to identify both endpoint section groups and uses `lem-weil-pbc-filtered-colimit-modules-elementwise` for the eventual-zero criterion. No uncited non-elementary fact is used.

I searched the whole DAG and blueprint for 01Z0, the item id, and the phrases `quasi-coherent sections descend`; no duplicate blueprint or DAG node was found. I ran the required Mathlib searches for the item and the new node: LeanFinder, Loogle, grep, and LeanSearch (LeanSearch was unavailable and recorded as unavailable). Mathlib has structure-sheaf affine-transition limit declarations, but no quasi-coherent-module section comparison or affine pushforward/tensor-colimit theorem, so both nodes remain project statements. Small-case checks: for an identity system the colimit map is the identity; for an affine stage the result reduces to the usual module base-change formula and filtered colimit of modules; the eventual-zero clause reduces to the defining zero criterion in a directed module colimit.

## Not duplicates

lem-sc-valuation-limit-affine-pushforward-colimit vs lem-sc-valuation-limit-qcoh-section-descent: the new node is the relative-spectrum and pushforward/tensor-colimit construction used as an intermediate proof input, while the item concludes the global-sections bijection and eventual-zero statement.
lem-sc-valuation-limit-affine-pushforward-colimit vs lem-weil-pbc-limit-global-sections-colimit: the existing node is only the structure-sheaf global-functions special case (and is a Mathlib leaf); the new node concerns pushforwards and tensor products for an arbitrary quasi-coherent module and does not assert the global-functions conclusion.

## Second reading by C1

- Item statement: checked against Limits Situation `descent` and Lemma 01Z0 (`lemma-descend-section`) hypothesis by hypothesis; the qcqs schemes, affine transitions, chosen stage, pullbacks, bijection, and eventual-zero consequence agree.
- Supporting node `lem-sc-valuation-limit-affine-pushforward-colimit`: checked against the first two paragraphs of Lemma 01Z0; relative spectrum, affine pushforward/tensor identities, tensor-colimit identification, and the qcqs global-sections comparison are stated explicitly.
- Step 1: checked against `lem-weil-pbc-limit-affine-transition`; cofinal-tail restriction and affine projections are the stated consequences.
- Step 2: checked against the supporting node; every relative-spectrum and tensor identification used by the step is stated there.
- Step 3: checked against the supporting node's added qcqs global-sections clause; this repairs the prior misuse of the affine-open-only colimit node on a non-affine qcqs scheme.
- Step 4: checked against the supporting node and `lem-weil-pbc-filtered-colimit-modules-elementwise`; endpoint section identifications and the eventual-zero criterion are exactly the cited conclusions.
- Small cases checked: identity system, affine stage, empty scheme, and zero module all reduce to the identity or zero colimit map.
- Changes: corrected the main node's `created.item` to this item; corrected its source label from nonexistent 01ZR to 01Z0; marked Step 4 non-elementary because it invokes the filtered-colimit zero criterion; added the qcqs global-sections clause and the existing relative-spectrum definition dependency to the supporting node.
