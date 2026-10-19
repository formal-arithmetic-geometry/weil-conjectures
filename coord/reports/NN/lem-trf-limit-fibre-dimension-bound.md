# Stage-1 delivery: lem-trf-limit-fibre-dimension-bound

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-limit-fibre-dimension-bound.json`: statement, split. No matching project declaration or Mathlib theorem found. Seven proof steps reduce the statement to the existing affine ring-system dimension bound. The hypotheses and conclusion are unchanged; doubled TeX escaping is corrected and explicit definition citations for fibre products and scheme-theoretic fibres are added.
- `citations.json`: one exact statement quotation for every node citation in every proof step.
- `report.md`: this report. `searches.jsonl` contains the actual msearch results; `write_split.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of `WeilConjectures/` in the provided slopmaster2 source for the exact blueprint id, limit/dimension combinations, fibre dimension and fiber dimension did not find a declaration giving this statement. The upstream master source was also searched for the exact id, Tag 05M5 and limit/dimension combinations; it supplies no attachment either.

## WANTED

None. All source material used is available locally.

## What needed correction

The imported item had no proof or proof dependencies. Its source statement is correct and is retained. Its JSON encoded TeX commands twice; these are now ordinary TeX commands. Its statement used fibre products and scheme-theoretic fibres without direct definition citations; these now have statement dependencies.

The existing node `lem-weil-pbc-affine-limit-fibre-dimension-bound` already proves the strictly affine ring-system case, including surjective comparison maps. Its dependency list and full proof were read: its proof does not use this item and replaces the problematic source diagram by stabilization of quotients of a fixed finite-type algebra over a residue field. Creating another affine bound or an equivalent clause would duplicate that node. The item therefore supplies the actual finite-chart globalization, with all comparison maps and persistence checks written out.

## Source error

In the local `limits.tex`, Tag 05M5 (`lemma-limit-dimension`), the final displayed diagram ends with an arrow from an earlier-stage fibre to the limit fibre `X_s`, followed by the claim that all arrows are closed immersions. Inverse systems supply arrows in the opposite direction: the limit maps to stages. A closed immersion from a stage into the limit is not generally available (already a system shrinking an affine line to its origin shows why). The subsequent claim about all components containing the chosen point also does not follow merely from choosing that point. These are errors in the printed proof, not counterexamples to the lemma. The independent affine proof in the existing DAG explicitly corrects this using a fixed ambient noetherian fibre algebra. This delivery uses only that node's statement and proves the globalization. Accordingly `proof_origin.by` is `agent`, with 05M5 as the source of the intended theorem; it does not claim that the erroneous paragraph was followed literally. No unit or target statement is changed and this is not a statement dispute.

## Mathlib and blueprint searches

The sandbox search log records fresh leanfinder, loogle, grep and leansearch queries for this item's full statement, plus a second semantic phrasing. I read the returned results: affine-transition-limit approximation and compactness results, finite-morphism fibre finiteness, and order-theoretic dimension bounds do not assert this eventual fibre bound. The grep hits concern probability, finite dimensional modules and homological dimension. No match was recorded as a leaf. The item's inherited search records remain present; the appended records correspond exactly to this worker's actual log. No new node requires its own searches.

Whole-DAG searches for 05M5, `lemma-limit-dimension`, local fibre dimension and affine limit bounds found the existing affine bound and the related local-dimension tools. `tools/blueprint_refs.py search '05M5'` returned no blueprint duplicate, `'fibre dimension'` returned only the unrelated projective-curve finite-group result, and `'affine limit'` returned sheaf/cohomological-dimension statements, not this bound. `ancestor` confirms `lem-trf-local-term-locality`; its recorded place and via ancestry are retained. The finite-stage bound remains a subsidiary input to the existing nearby-cycle/semistable-alteration branch of that ancestor, not a replacement of the unit's route.

## Not duplicates

No new nodes are introduced. The existing affine node is a strictly special case with rings and tensor-surjectivity hypotheses. The present item allows nonaffine qcqs bases and nonaffine finite-type sources; its proof gives the finite-cover reduction rather than renaming the affine case.

## Review by NN

I read the complete 05M5 statement and proof in `literature/stacks-project/limits.tex`, and checked that its four assumptions are exactly those of the item: affine base transitions, qcqs bases, finite-type morphisms, and closed immersion comparisons. I read the recorded chapter and unit and the parent pure-relative-dimension split to locate this auxiliary result on the required route. No new node or source statement was invented. For the supporting facts I read the node statements and the local Stacks passages: 01YW/01YX for affine limits, 01QO for closed immersions on affine charts, 01QR for base change of closed immersions, 01T2 for locally finite type on arbitrary affine pairs, 0055 and 0B7I for local/global dimension, and 00P4/02FY for field-extension/local-fibre-dimension invariance. The affine-cover Mathlib statement was read at `Morphisms/QuasiCompact.lean:85`. The quoted fibre-product and open-immersion base-change nodes supply exactly their usual universal property/affineness and open-immersion assertions, respectively.

Step 1 uses the finite affine cover node only for the qc scheme S_i0; finite source covers are supplied directly by the finite-type definition. It does not assume X_i is separated or quasi-separated. The cofinal-tail construction is written out and uses a common upper bound to prove independence. The fibre-product and open-immersion definitions specify the open inverse images and their covering property.

Step 2 uses closed-immersion base change to restrict the hypothesis comparison, the affine fibre-product statement to make its target affine, and the affine closed-immersion criterion to make its source affine and the coordinate map surjective. I checked the restricted source really is W_j,a by the projection equations; it is not a factorization inferred from set containment. The affine-pairs node says finite type for EVERY pair of affine opens in a locally finite-type morphism, so it applies directly to f_i and the chosen W_i,a and V_i,b. This avoids assuming an arbitrary affine restriction has finite type solely from the definition without the characterization theorem.

Step 3 proves the chart-limit identification on maps from every test scheme, using the fibre-product universal property and the given limit X. Its affine representation then follows from the affine clause of the limit theorem; the affine-local-target statement verifies its transition hypothesis on the singleton target cover. There is no use of an unproved global affineness assertion for X_j to X_i, and no smallness issue beyond the stated directed SET.

Step 4 uses the open-immersion base-change statement to obtain open chart fibres, open-subspace local-dimension invariance to compare their points, the definition to bound local dimension by global dimension, and 0B7I to bound the chart fibre. The affine fibre-product statement gives exactly the spectrum of the tensor-product fibre ring needed for the affine bound. Restriction to an open base preserves local rings and therefore residue fields. No finite presentation or flatness assumption was added.

Step 5 invokes only the STATEMENT of the existing affine bound. All its finite-type, tensor-surjectivity, colimit and fibre hypotheses were verified in Steps 2–4, and the directed tail is nonempty. I checked its dependencies do not return to this item. Its internal stabilization argument is not used as a black-box clause absent from its statement.

Step 6 uses 01QR to get the closed immersion on the actual fibre and 02FY to preserve local dimensions after the residue-field extension. The chart morphism is locally finite type because Step 2 supplies its finite-type affine coordinate map. The local dimension inequality for a closed subspace is proved from irreducible closed chains and open neighbourhoods in the step; it is not cited without a node or promoted to a new lemma. Supremum of the local bounds gives the whole-fibre bound. Thus the finitely many witness indices in Step 5 can legitimately be replaced by their common upper bound.

Step 7 again uses only open-immersion base change, local dimension on opens, and the supremum formula. The source charts cover X_j, so each fibre point belongs to one of them even when the base charts overlap. This proves the global bound without assuming irreducible components stay inside one affine chart. Empty fibres have dimension minus infinity, the zero bound d=0 works without change, and an empty initial source is handled before selecting witnesses. Constant systems and a singleton index also satisfy each construction. The proof permits nonreduced schemes and arbitrary residue-field extensions.

I checked delivery-errors B–E against these files: there are no unsplit new nodes with hidden proofs, no duplicate or restated item clause, no uncited non-elementary invocation, no added hypothesis, and no forward/circular citation. Each `uses` id has its literal statement quotation in `citations.json`; every proof dependency is used. All seven steps are below 2000 characters, and their elementary subarguments are written in the steps. Off-unit generic tools that require declaration are listed in `split_report.tool_uses`; this finite-chart localization does not alter the trace-formula unit's route. No Lean was written or compiled, and all writes were confined to this item's sandbox.

## Unfinished work

None in the stage-1 split. The required remote dry run and push follow this report; their output determines delivery success.
