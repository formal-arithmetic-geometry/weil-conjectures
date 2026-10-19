## Worker report

Files written:

- `dag/nodes/sec-purity-real-sheaves/lem-a1-scheme-lqf-etale-source-locality.json`: item, split in seven steps; statement unchanged.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-scheme-lqf-affine-criterion.json`: statement, unsplit; no exact Mathlib match for the Stacks finite-type and isolated-fibre notion.
- `dag/nodes/sec-purity-real-sheaves/lem-a1-lft-flat-lfp-source-descent.json`: statement, unsplit; no exact Mathlib match for source-triangle descent.
- `citations.json`: verbatim statement quotations for every use in every numbered step.

Attachments: none. Searched the read-only slopmaster2 `WeilConjectures/` by the item id, LocallyQuasiFinite, etale/source/surjective combinations, and local-finite-type source descent. The existing project `LocallyQuasiFinite.of_etale` supplies only a Mathlib-predicate forward component, and does not state this item. No complete project attachment for the item or the two new nodes was found.

WANTED: none.

The item was an unsplit statement created in N5's earlier split. Its statement agrees with Stacks 03X4, and needs no correction. Its existing Mathlib search records were retained and their candidate conclusions were checked against the actual source. Mathlib's `LocallyQuasiFinite` omits local finite type. Neither its `of_comp` lemma (which concludes a property of the first arrow) nor its composition instance proves descent through a surjective etale source cover in the Stacks sense. Likewise Mathlib's `DescendsAlong` instances mean pullback descent, not an arbitrary triangle. Misreading the semantic search summaries would have incorrectly made these leaves.

Read the chapter and Rankin–Selberg unit records, and the current main-20261015 `lem-a1-affine-hc0.md` and `.proof.md`. The current blueprint proof is the lisse-support proof. This item belongs to the inherited auxiliary schemehood branch through separated etale algebraic spaces; its split supplies that branch's generic chart-comparison input and changes no unit or chapter. Both new nodes retain this complete ancestry and exact purpose. The item is not the unit's key node, so no unit realization file was changed.

Nothing remains unfinished in this one-level split. The two new statements intentionally have no proofs or proof dependencies and join the next stage-1 frontier. All Mathlib searches used the mandated msearch command and their returned records are preserved in searches.jsonl and the corresponding nodes. LeanSearch, Loogle, LeanFinder and source grep all responded. Second semantic phrasings were tried for the item and both new statements. No Lean was written or compiled.

## Not duplicates

lem-a1-lft-flat-lfp-source-descent vs thm-pd-fpqc-local-properties: the existing node cites 02KL but states descent for a scheme over a finite field extension with smoothness, properness and connectedness. It does not state local finite type descent for an arbitrary triangle with a flat surjective locally finitely presented source arrow.

lem-a1-scheme-lqf-affine-criterion vs pqf-def-quasifinite: the existing definition provides an existential affine witness at each point; 01TK proves the all-affine-pairs characterization and the arbitrary open-cover gluing equivalence.

lem-a1-scheme-lqf-affine-criterion vs lem-weil-pbc-lqf-restriction-to-opens: the existing result is the restriction implication, not the all-affine-pairs or gluing characterization.

Searches of the whole DAG for 01TK, 02KL, 0367, local quasi-finiteness, affine chart criteria and local finite type source descent found no other matching statement. Whole-blueprint searches used `quasi-finite`, `locally quasi-finite`, `01TK`, `036H`, `02KL`, `finite type`, `finite presentation`, `affine opens`, and `surjective flat`. None states either new node. The apparent additional 02KL occurrences in search-result hashes are unrelated to the Stacks tag.

## Review by N1

I read Stacks `descent.tex`, Tag 03X4 (`lemma-locally-quasi-finite-etale-local-source`) and its full proof, and Tag 02KL (`lemma-flat-finitely-presented-permanence`) including the finite-type alternative and its proof through 0367. I also read 0367's actual ring statement: the second arrow must be faithfully flat AND finitely presented. I did not replace that theorem with unrestricted faithfully-flat source descent. For the new affine-criterion node I read `morphisms.tex`, Tag 01TK (`lemma-locally-quasi-finite-characterize`), statement and proof. Its three clauses, arbitrary open covers, and lack of Noetherian or separation assumptions agree with the new statement. The second new node is exactly the local-finite-type alternative of 02KL, with every scheme and arrow introduced and with point-surjectivity stated explicitly.

For step 1, I opened the definitions of etale, flat, local finite presentation, unramified and open immersion. The argument uses the same local rings and presentations and the restricted diagonal, not an unproved descent result. Local finite presentation also gives local finite type directly because a finite presentation has finitely many generators. Restriction of an open immersion is still an isomorphism onto an open subscheme, directly from the cited definition. The only surjectivity inference is that a preimage of a point in an open belongs to its inverse image.

For step 2, I read the new affine criterion, `lem-weil-pbc-etale-ring-map-quasi-finite`, `lem-trf-quasi-finite-composition`, and `pqf-def-quasifinite`. The first gives finite type and quasi-finiteness at ALL primes for the g chart, the second gives both for the p chart, and the composition theorem explicitly preserves both. Thus none is being used merely by its title or its proof. Choosing an affine neighbourhood inside each inverse-image open guarantees the maps of rings really compose. The composite ring map gives the precise existential witness required by the definition at the chosen u.

For step 3, `lem-weil-pbc-lqf-locally-finite-type` states exactly the implication used. The etale definition supplies both flatness and local finite presentation, and assumed surjectivity supplies the remaining hypothesis of the new 02KL node. This is arbitrary source descent; no pullback square is invented and no quasi-compactness is assumed.

For step 4, I read the statement of `lem-weil-pbc-etale-covering-affine-refinement`: its target is affine, its family is jointly surjective and etale, and its conclusion gives finitely many affine OPEN pieces of the source with images covering W. These are exactly the hypotheses and conclusion needed here. `lem-weil-pbc-lqf-restriction-to-opens` allows separate opens in source and target, so it applies to A_j and Z without requiring A_j to be the whole inverse image of Z.

For step 5, I opened `lem-weil-pbc-morphism-affine-schemes-affine` and clause (3) of `lem-weil-pbc-affine-morphism-permanence`: together they give quasi-compactness of each A_j to Z map. `pqf-lem-qf-locqf-qc` supplies quasi-finiteness, and `pqf-lem-qf-finitefibres` explicitly gives finite fibres. I also read the corresponding Stacks 01TJ and 02NH statements. No finite type or quasi-compactness of the original cover p is used.

Step 6 is the actual finite-image argument: a point w over t lifts to one A_j because their images cover W; its lift automatically lies over t. This gives an equality of sets, not merely a containment. Finite images and finite unions then prove the desired finite fibre. There is no scheme-theoretic lifting or unjustified factorization through a subset.

For step 7, I read both directions of `lem-weil-pbc-lft-affine-pairs` and the definition of finite type. Their use on subcharts makes the restricted W to Z map locally of finite type, and the same two affine-permanence statements supply quasi-compactness. Thus every hypothesis in the EXISTING finite-fibre characterization is present before it is applied. The final gluing uses clause (3) of the new 01TK node on a genuine target cover and covers of its inverse images. It does not take finiteness of whole fibres of g from an infinite source cover.

Small cases checked: the zero ring/empty affine chart; the empty refined family (which forces W empty); a nonsurjective open immersion p (only the forward assertion is claimed); an infinite disjoint union of identity etale maps (p need not be quasi-compact); and arbitrary non-Noetherian affine bases. The affine criterion admits an infinite union of points over a field and imposes no global quasi-compactness. The 02KL node admits such infinite source covers as its source does. No separability is imposed on g. Neither new node is elementary or a restatement of either etale-locality clause: the first is the general non-etale affine comparison/gluing theorem, and the second descends finite type alone under the more general flat-lfp hypothesis. Every non-elementary input has a cited node. All seven steps are below 2000 characters.

Generic off-unit geometry inputs are declared in `split_report.tool_uses` with their role in the 03X4 proof. I corrected no mathematical statement. The explicit finite refinement, finite-image equality and the distinction between Mathlib predicates and the Stacks predicates are the substantive repairs to the previously empty proof. The report is my direct-delivery review; the maintainer still supplies the independent review.
