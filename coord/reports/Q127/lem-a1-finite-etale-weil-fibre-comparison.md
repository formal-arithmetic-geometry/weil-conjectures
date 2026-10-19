# Q127: lem-a1-finite-etale-weil-fibre-comparison

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-finite-etale-weil-fibre-comparison.json`: statement node, now split into ten steps. Mathlib searches found no statement of the rational Weil comparison. No new nodes or Mathlib leaves.
- `citations.json`: one unmodified statement quotation for every step/node citation. Whole statements are quoted so qualifications remain visible.
- `report.md`: this report. `searches.jsonl` retains the search command's original output records; `build_split.py` is sandbox-only preparation material.

## Attachments

None. I searched the project source under `WeilConjectures/` for the exact blueprint tag and for finite direct image, stalks, and Frobenius. The ordinary finite-stalk isomorphism in `WeilConjectures/SixFunctors/Finite/Stalk.lean` and ordinary finite base change in `Finite/BaseChange.lean` do not state rational/common-stage Weil coefficients, residue-field base restriction, or the two operator comparisons. The finite-cycle discussion in `DeligneLaumon/Reduction/FormalSteps.lean` does not provide a completed proof of this item. I also checked the read-only upstream master reference; sorry-bearing reference declarations were not treated as completed proofs. The item's current node has no attached `lean_audit` declaration to account for.

## WANTED

None.

## Statement, route and searches

I retained every hypothesis and conclusion. In particular, I did not add separatedness of the schemes, although `lem-zl-finite-adic-direct-image` requires it. The proof first establishes that the actual normalized coefficient-tower direct image exists globally, then uses that rational finite-stalk theorem only on affine neighborhoods. Finite morphisms themselves are separated; this is sufficient for the Weil-operations tool and does not require separated source or target structure morphisms.

The current blueprint ancestor is `lem-a1-finite-map-purity`, first paragraph, in `literature/blueprint/main-20261015/`. This item's contribution is the geometric-fibre comparison at a closed point and identification of the local return operators. The cyclic decomposition and eigenvalue argument stay in the existing `lem-a1-finite-weil-sections-decomposition` and the parent, respectively. The ancestor/unit records were read; this item is not the unit's key node, so no unit record is changed.

Before choosing dependencies I searched the full DAG by the finite-stalk/Frobenius/residue-field notions and Stacks Tags 03QP and 04HN, and used `tools/blueprint_refs.py` to search and locate the ancestor. I read the complete statements of the dependencies used below. No new node was necessary: the extra arguments are finite products, affine localization, expansion of the explicitly defined iterates, and residue-field algebra from the cited statements. In particular I did not create a node merely for a clause of the item or a nonseparated variant of the finite-adic lemma. The blueprint-wide searches found no other blueprint statement of this full comparison; `same_as` remains empty.

Mathlib searches were run only through the authorized `msearch.py` command. I read both LeanFinder phrasings, the quoted `stalkPushforward` Loogle results, the grep results and the LeanSearch results. They concern ordinary topological stalk maps, finiteness of scheme fibres, or arithmetic Frobenius of fields, rather than rational Weil sheaves. The five additional search records in the node reproduce the tool and query strings in the sandbox log. Previous Q148 search records are preserved rather than rewritten as searches by Q127.

## Review by Q127

For the item I read Stacks `etale-cohomology.tex`, Tag 03QP (`proposition-finite-higher-direct-image-zero`), including its strict-henselian proof, and the adjacent finite base-change argument, Tag 0959. This is a finite-level theorem, not a theorem about rational Weil coefficients. I also read `etale.tex`, Tag 04HN, for finite-etale splitting. Deligne, Weil II (1.1.3), (1.1.7)--(1.1.10), printed pp.150--152, supplies the finite coefficient-field convention, geometric Frobenius convention, and behavior under extension of the finite base field. I read Bhatt--Scholze Proposition 6.8.14 and Remark 6.8.15 for the distinction between rationalization and discrete coefficients. The resulting proof is marked agent-written: these sources do not literally state the whole rational equivariant comparison. There are no new nodes requiring separate source claims, and no SGA route is used.

Step 1 uses the actual finite-etale splitting statement, which permits an empty set of sheets. The pro-etale restriction/injectives statement applies to the etale neighborhoods because etale maps are weakly etale. On each sheet pushforward is restriction; finite sums are exact and commute with derived scalar change. These are explicit computations, not an invocation of arbitrary pushforward exactness. For constructibility, the pro-etale-origin equivalence applies at each finite ring, and `fin4-thm-finite-morphisms-constructible` says both constructibility and vanishing for a finite morphism with finite-type target. It does not require separated source or target. The comparison with etale pushforward is checked on the same sheets.

Step 2 uses the integral category definition for a *single interval independent of n*, the full normalized-tower definition for coherent transition maps and the quotient cocycle, and the effectivity theorem for canonical recovery of every finite reduction. I checked that effectivity by itself asserts neither boundedness nor constructibility: these are supplied by Step 1 with the same interval as the input. The direct-image definition uses this very derived-limit tower. No finite-Tor assumption is smuggled into a reduction theorem.

Step 3 uses finite-morphism permanence to get affine inverse images, so that the separated hypotheses of `lem-zl-finite-adic-direct-image` really hold on each chart. The finite-coefficient open-restriction theorem provides its canonical comparison. The ringed-site exact restriction/extension-by-zero adjunction justifies commuting restriction with the derived tower limit, and open-factor coherence identifies completed restriction with ordinary restriction. The constructible truncation and local fibre criteria supply the standard heart interpretation and checking on separated opens. A finite cover, rather than an unbounded family of local coefficient denominators, is used to infer rational vanishing. The resulting stalk comparison is the restriction map of the finite-adic lemma and inherits its semilinear diagram naturality.

Step 4 checks the domain clause of `lem-fix-weil-operations`: it gives equivariance only *after* bounded constructibility has been established. Finiteness makes the morphism proper and separated. Thus the argument does not use Weil equivariance as a fictitious constructibility theorem. The induced structure is explicitly exchange followed by pushforward of the given structure.

Step 5 uses closed-point field finiteness, finite base-change permanence, properness of finite maps, closed-immersion base change, and the closed-immersion residue-field isomorphism exactly as stated. The affine quotient calculation identifies points over y, and the finite-dimensional-domain calculation shows their residue fields finite over L. The closed-point criterion then proves they are closed in X0, even when X0 is not separated. Thus no claim about arbitrary closed fibres or general prime tensor products is being taken from a definition node.

Step 6 uses the integral pullback-preservation statement for constructibility and its actual finite-reduction comparison. The fibre criterion is used on separated affine charts and on the finite scheme Z, not applied globally outside its hypotheses. The return identity uses the dy-th power of base Frobenius because the chosen embedding L into k is fixed by precisely that return. Pullback composition supplies the specified associativity comparisons. The sheaf G is a restriction with a genuine specified isomorphism eta; it is not an object chosen from an existence theorem or an unrelated descent assertion.

Step 7 takes the underlying stalk isomorphism from the finite-adic node and uses the proper-coincidence Frobenius node on Z0/L. Its properness was proved in Step 5. That node explicitly supplies an isomorphism from compact to ordinary cohomology, so the required direction of b is its inverse after the ordinary restriction map.

Step 8 reads the semilinear naturality clause of the finite-adic node, rather than assuming naturality in sheaf morphisms also means naturality under base-field automorphisms. Both clauses are in its statement. I checked the explicit naturality formula in the point-transport node, and the local and global operator definitions; the source uses dy point transports, while the fibre uses one L-Frobenius transport with the same base automorphism. The transport-isomorphism node is applicable to the separated finite scheme Z0 over L. Proper-coincidence clause (2) is exactly the compatibility needed to pass from ordinary to compact cohomology. This proves equality of operators, not just equality of traces.

Step 9 expands both operators at a point with e=[kappa(x):L]. The fields and lifts are already identified in Step 5. Both expressions have edy structure factors and edy point-transport factors, with the same ordering. I checked that the composition node states associativity, and that the transport node states naturality, rather than citing merely definitions for these coherence facts. No equality of scheme maps of the form phi^r xbar=xbar is used; the correct return is phi^r xbar=xbar gamma_s^r.

Step 10 uses the common-stage coefficient definition to represent the object, morphisms, inverse and equations together. The finite-adic node and point-transport node both explicitly include scalar-extension compatibility. Thus the passage to Qbar does not assume one global integral Weil lattice. Empty fibres, the zero sheaf, degree-one points, and disjoint components satisfy all formulas; no ordering of the fibre, nonzero-stalk condition, purity, lissity or semisimplicity enters. Finite etaleness excludes nilpotent fibres in this item, and no reducedness argument is needed.

I checked delivery-errors B through E against the finished node: every non-elementary input has a node, no step substitutes a definition for a theorem, each dependency's coefficient domain and separatedness hypotheses are matched, and the proof contains no renamed clause serving as a new lemma. All ten steps are shorter than 2000 characters. The main corrections to the initial plan were the explicit normalized-tower construction and affine localization, so the separated-only rational finite-adic lemma is not applied to a nonseparated scheme. `citations.json` preserves the full verbatim statements, including the qualifications just discussed.

## Not duplicates

No new nodes. `lem-zl-finite-adic-direct-image` is reused on separated affine charts, rather than duplicated with relaxed separatedness hypotheses. `lem-a1-finite-weil-sections-decomposition` is retained as the separate finite-cycle input to the parent, rather than restated here.

## Unfinished work

None in the stage-1 split. Stage-2 Lean statements and stage-3 proofs are outside this assignment. Delivery preflight and push are performed after this report is written.
