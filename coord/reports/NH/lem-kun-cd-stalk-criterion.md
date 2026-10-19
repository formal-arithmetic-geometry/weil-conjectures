# Stage 1 report: lem-kun-cd-stalk-criterion

## Files written

- `dag/nodes/sec-smooth-purity/lem-kun-cd-stalk-criterion.json`: item split into three proof steps; no new nodes.
- `citations.json`: verbatim statement quotes for every cited node in every step.

## Attachments

None. No sorry-free declaration in `WeilConjectures/` of either `/home/ubuntu/weil-conjectures-slopmaster2` or `/home/ubuntu/weil-newtargets-master` carries this exact statement.

## WANTED:

None.

## What was checked and corrected

The imported proof had one paragraph and omitted the actual higher-direct-image presheaf lemma. I checked the blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-cd-stalk-criterion.md`, the item statement, and all cited node statements. Step 1 now explicitly uses `sbc-lem-higher-direct-image-presheaf`, whose statement gives the sheafification of the presheaf `W ↦ H^q(W ×_Y X, F|...)` (Stacks Tag 03Q8). Step 2 uses `lem-weil-pbc-sheafification-geometric-stalk`, which states that sheafification preserves the geometric stalk, and `def-weil-pbc-geometric-stalks`, which states that the stalk is the filtered colimit over pointed etale neighbourhoods. Step 3 uses `lemma-weil-pbc-geometric-stalk-conservative`; its statement says exactly that a sheaf morphism is an isomorphism iff it is so on every geometric stalk, applied to the zero morphism into `R^q f_* F`. I verified the quasi-compact/quasi-separated, torsion, `q ≥ 0`, and geometric-point hypotheses are those of the item and are not strengthened by any step. `citations.json` quotes the exact sentences/formulas used.

I searched the complete DAG and blueprint for the target and for the proof facts. The only related existing statement needed is the higher-direct-image presheaf node above; no duplicate node was created. The target was searched with LeanFinder, Loogle, and Mathlib grep in two phrasings; the recorded searches found no exact Mathlib criterion. I also searched both read-only upstream source checkouts by target id and key terms and found no declaration.

## Review by NH

I read the source node and its blueprint proof, then opened each cited node and compared its statement to the precise fact used. Step 1 takes only the sheafification/presheaf formula from `sbc-lem-higher-direct-image-presheaf`; Step 2 takes stalk invariance under sheafification and the colimit definition from the two cited nodes; Step 3 takes only stalk conservativity from `lemma-weil-pbc-geometric-stalk-conservative`. The zero-morphism application is elementary category reasoning from that statement. I checked that the neighbourhood indexing and restriction of `F` agree with the item, and that no source hypothesis is silently dropped. I corrected the imported proof by citing the existing higher-direct-image presheaf node and by separating the sheafification-stalk identification from the conservativity argument. No new node was needed, and no statement error was found.

## Earlier second reading (a previous round; superseded)

- Item statement: compared verbatim with `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-cd-stalk-criterion.md`; qcqs morphism, nonnegative degree, torsion abelian etale sheaf, all geometric points, and all pointed etale neighbourhoods agree. No statement dispute. The parent unit and chapter are unchanged.
- Step 1: opened `sbc-lem-higher-direct-image-presheaf` and Stacks Tag 03Q8, `etale-cohomology.tex`, label `lemma-higher-direct-images`; its abelian-sheaf clause applies with h=f and gives exactly the required sheafification. No qcqs or torsion hypothesis is needed for this tool. Corrected the step's source file from sites-cohomology.tex to etale-cohomology.tex and supplied the label.
- Step 2: opened `lem-weil-pbc-sheafification-geometric-stalk` and `def-weil-pbc-geometric-stalks` against Tag 03PT (2), label `lemma-stalk-exact`, and the local stalk definition. Their statements give the canonical isomorphism, including the presheaf stalk; made the opposite neighbourhood indexing explicit. This step uses no limit-scheme continuity or identification with fibre cohomology.
- Step 3: opened `lemma-weil-pbc-geometric-stalk-conservative` against Tag 03PU, label `theorem-exactness-stalks`; isomorphism detection follows from the injective and surjective clauses. Its statement applies to the abelian-sheaf morphism 0 to G. Expanded the elementary facts that the colimit of zero groups is zero and that 0 to a group (or an abelian-category object) is invertible precisely when that object is zero. The use of conservativity itself remains non-elementary and cited.
- New nodes: none. B1--B7, new-node duplicate tests, and new-node Mathlib searches are vacuous; the proof uses four existing nodes, each opened and quoted in citations.json. No unsplit clause of the item was moved to another node.
- Small cases: F=0 gives zero values and zero higher image; Y empty has no geometric points and only the zero abelian sheaf; f=id over a separably closed field at q=0 gives the usual stalk test, whereas positive q gives zero. For general f at q=0 the formula is sections on the base change, and at q=1 it is their first cohomology, with precisely the same sheafification argument. No edge case excludes zero objects, empty schemes, or degree zero.

Changes: corrected the 03Q8 source file and exact labels; clarified opposite indexing and wrote the zero-object argument explicitly. The statement, dependencies, and original review remain intact. All citation quotes remain verbatim parts of the opened node statements.

The higher-direct-image formula, sheafification-stalk lemma, and stalk-conservativity lemma are generic tools from other units, used as black boxes; they supply the blueprint's existing presheaf/stalk argument without replacing any unit step. Their accepted tool-use bookkeeping belongs to the maintainer (C8); no tool_uses field was written here.

## Repair of returned points (2026-10-14)

I repaired each point in the return review. The statement now includes
`def-weil-pbc-direct-image` as a statement dependency because the notation
`R^q f_*F` is defined there. The proof provenance is marked `by: agent`,
since the cited blueprint is an agent-authored route rather than a literature
source. The split report declares the three cross-unit generic lemmas as
`tool_uses`, with the exact fact each step takes from them. I reran the
required Mathlib searches through `msearch.py`, including a second phrasing;
the new record preserves the unavailable LeanSearch result and records the
actual stalk-isomorphism hits and grep query. The existing search entries and
all citation quotes remain consistent with the node statements.

## Second reading by NH

- Item statement: checked against the blueprint node and its listed hypotheses; qcqs f, q >= 0, torsion etale F, all geometric points, and the pointed-neighbourhood colimit agree. Verdict: PASS; the direct-image definition is now a statement dependency.
- Step 1: checked against `sbc-lem-higher-direct-image-presheaf` and Stacks Tag 03Q8; its abelian-sheaf clause gives exactly the sheafification of the restricted cohomology presheaf. Verdict: PASS.
- Step 2: checked against `lem-weil-pbc-sheafification-geometric-stalk` and `def-weil-pbc-geometric-stalks`; both the stalk isomorphism and opposite pointed-neighbourhood indexing are stated there. Verdict: PASS.
- Step 3: checked against `lemma-weil-pbc-geometric-stalk-conservative`; the zero morphism argument uses only its stalkwise-isomorphism criterion and elementary zero-object facts. Verdict: PASS.
- New nodes: none; therefore B1--B7, duplicate checks, and new-node Mathlib searches are vacuous. Existing cross-unit nodes were opened and are recorded as tool uses.

Changes made during this second reading: no further mathematical edits were needed; the prior repair's direct-image statement dependency, agent proof provenance, tool-use declarations, source correction, explicit opposite indexing, and expanded zero-object argument were verified. The delivery dry run was then rerun with the supported two-argument command.
