# Worker report: lem-sfb-bounded-extension-zorn

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-bounded-extension-zorn.json`: statement, split; five explicit proof steps and the existing Mathlib leaf `lem-weil-pbc-zorn-lemma`. No new nodes and no new Mathlib leaves.
- `citations.json`: the verbatim statement of the Zorn node, used in step 4.
- `searches.jsonl`: six actual searches made through the required msearch command; their exact tool/query/results records are appended to the item without deleting its inherited search history.
- `report.md`: this report.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag, bounded-extension terminology and Zorn. There is no declaration stating this item. The only close project analysis source is `lean/Sheaf/Analysis/Normed/Module/ProperUltrametricScalarExtension.lean`: lines 62–69 explain the argument in its docstring, but its theorem ends in `sorry` and states the stronger parent under proper ultrametric field assumptions. It is not an attachment. The project p-basis maximality results concern different partial objects.

## WANTED

No missing reference is needed to justify the present conditional Zorn argument: its only non-elementary input is already the existing Mathlib Zorn leaf. The inherited source records the parent reference A. W. Ingleton, *The Hahn-Banach theorem for non-Archimedean valued fields*, as WANTED; this item neither assumes nor cites that theorem. Its local extension hypothesis explicitly supplies the analytic input.

## Findings and corrections

The imported statement is sound and is unchanged, including all chain and maximality clauses and the absence of completeness, closedness and nontrivial absolute-value hypotheses. The item had no proof. I supplied the graph argument rather than adding a node that repeated the conclusion or the chain-union clause. All uses of norm and linearity are evaluations inside one member graph with the same fixed constant C. No continuity or choice of a new bound is needed.

The current blueprint proof at `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3), does not contain the scalar-extension expansion. I read it and retained agent proof provenance, as explicitly recorded in the inherited source and the parent. The parent's old steps 5–6, also retained in the Sheaf docstring, give exactly the intended chain/Zorn route. I read the chapter and unit records and SETUP's three-level rule; this generic scalar-extension tool changes no part of that route. The item is not the unit's key statement, so no unit realization file is written.

The ancestor command returns `None` because this created-item chain ultimately points to a non-node module. I retained the inherited null `blueprint.from.node` and its via list, with the actual blueprint source anchor named in `split_report.blueprint`; the parent's existing independent review explicitly accepted this same ancestry condition. The existing `from.place` already specifies the precise old steps 5–6 and is retained. Searches of the whole blueprint for `Zorn`, `bounded partial`, and `linear functional` found no equivalent blueprint node. The latter search returned only `sk-def-kernel`, an unrelated Fourier kernel. `blueprint.same_as` is empty.

## Mathlib searches and candidate reading

I ran LeanFinder and LeanSearch in words, Loogle on `"LinearPMap", "exists"`, and grep on `LinearAlgebra/LinearPMap.lean`, then a second LeanFinder phrasing and second grep pattern. The exact records are in `searches.jsonl` and the item. All six services returned successfully.

I read `LinearAlgebra/LinearPMap.lean:583–655`: directed suprema construct the union map and evaluate it on its constituent domains, without a fixed-bound predicate or a conditional global extension conclusion. I read `Algebra/Module/Injective.lean:97–100,160–170,209–216,375–380`: Baer extension objects contain no bound, so their maximal extensions need not be bounded. HahnEmbedding hits assume an ordered Archimedean scalar field and describe Hahn embeddings. I read `Analysis/Normed/Module/HahnBanach.lean:40–46` and `Analysis/LocallyConvex/HahnBanach.lean:92–96`; they require `IsRCLikeNormedField`. `Analysis/Convex/Cone/Extension.lean:160–164` is a real Hahn–Banach theorem. Dense-range extension candidates require density, and algebraic `LinearMap.exists_extend` carries no norm bound. None states every clause of this item with its hypotheses. This remains a split, not a Mathlib leaf.

## Not duplicates

No new node is created. The DAG search for Zorn found the existing `lem-weil-pbc-zorn-lemma`, which is reused without alteration. Its `zorn_subset` match was read in `Mathlib/Order/Zorn.lean:143–145`. The parent and this item are the only bounded partial-extension hits relevant to this statement; the parent requires compact balls and proves local extendability, whereas this item assumes local extendability and proves the graph/maximality conclusions. No duplicate is introduced.

## Review by Q100

I read delivery-errors B–E in full, then reviewed the actual source text, the parent, the current item and the full statements of both dependencies. `def-weil-field` says precisely that K is a commutative ring with nonzero 1 and inverses for nonzero elements. All additional normed vector-space and graph notions are defined inline in the unchanged item, so no unstated definition is imported.

Step 1 uses only set inclusion and the given map f. I checked that f itself satisfies every membership condition for S, so the empty chain has an upper bound even if V=W=0. Step 2 defines the union graph's domain and proves single-valuedness by putting two purported values into the larger member of the chain. Nonemptiness is used exactly where needed to show that this domain contains W; the empty chain is handled separately. Step 3 puts two vectors into one member graph and writes down the resulting additivity and scalar identities. Zero lies in W, and every bound is obtained from a member containing the relevant pair, so the union is a bounded linear extension on a subspace. These are elementary calculations from the fully specified graph definitions, not a hidden union-of-linear-maps theorem.

Step 4 cites only `lem-weil-pbc-zorn-lemma`. I opened that node: its statement quantifies over a set of subsets of any set X, requires upper bounds for all inclusion chains including the empty one, and concludes precisely maximality in S. Here X=V×K is a set and S is a subset of its powerset. Steps 1–3 meet every hypothesis, and citations.json quotes the node statement verbatim. This Mathlib leaf is exempt from unit-route restrictions; no off-route theorem is substituted for a unit step.

Step 5 treats an arbitrary maximal member, not just the one selected by Zorn. Membership provides all hypotheses for the local extension assumption on its actual domain U and map g. The extending graph still restricts to f and retains the fixed bound. The pair at x belongs to that graph since x=0+1x, but not to the old graph since x is outside U, proving strict enlargement explicitly. Applying the resulting full-domain conclusion to the existing maximal member gives the promised h. No external analytic theorem is hidden in this step: local extendability is a hypothesis of the item.

I tested V=0; W=V (the initial graph is already the only possible extension); W=0 and f=0; singleton chains; chains with repeated domains (comparability then forces identical values); empty chains; and a trivially valued scalar field. The argument uses neither completeness nor nontriviality of the absolute value. Positivity of C is retained but not additionally used. No false statement, circular dependency, source error, new lemma disguised as a clause, or unproved compatibility remains. Each step has fewer than 600 characters, and the full proof has 2297 characters, so there is no long step hiding another lemma. No SGA source is used.

## Unfinished work

None in the one-level split. Delivery checks and push follow below.
