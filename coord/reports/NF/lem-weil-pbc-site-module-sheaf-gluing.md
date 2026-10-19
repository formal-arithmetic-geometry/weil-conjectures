# Stage 1 report

Files written:
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-sheaf-gluing.json` — statement node, unsplit, Mathlib no match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-site-module-sheaf-gluing.json` — split item.
- `citations.json`.

Attachments: none.

WANTED: none.

The existing `lem-weil-pbc-glue-sheaves-of-modules` is restricted to open covers of a topological space, so it cannot state the arbitrary-site covering assertion here. I created the strictly smaller arbitrary-site sheaf-of-sets gluing node from Stacks Tag 04TR and used it in the item's proof. The module operations are transported componentwise and checked on the covering.

## Not duplicates

`lem-weil-pbc-site-sheaf-gluing` vs `lem-weil-pbc-glue-sheaves-of-modules`: the new node is for sheaves of sets on arbitrary slice sites and arbitrary covering families; the existing node is for modules on open subsets of a topological space.

## Review by NF

I read the item source in `literature/stacks-project/sites.tex`, Tag 04TR, and the upstream TwoColimit `(Obj)` paragraph referenced by the blueprint. I also read the existing open-cover module-gluing node and confirmed its hypotheses do not cover arbitrary sites. Step 1 cites the new node's exact existence and overlap conclusion. Step 2 uses its existence of local sheaves together with the module-sheaf and localized-ring definitions to transport operations and verify them locally. Step 3 uses the exact overlap equation from the new node. I checked the one-index-cover and identity-transition cases; both reduce to the original sheaf and module. Mathlib searches were run for both the item and the new node; available hits concern section gluing or already-given sheaves, so neither statement is a Mathlib leaf.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-site-module-sheaf-gluing: underlying sheaves of sets on arbitrary sites versus sheaves of modules with ring actions.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-connected-torsor-module-descent: arbitrary site sheaf gluing versus connected torsor equivariant module descent.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-associated-module-comparisons: arbitrary site sheaf gluing versus comparisons for a torsor-associated module.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-module-descent-equivalence: arbitrary site sheaf gluing versus equivalence for torsor module descent.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-ordinary-evaluation: arbitrary site sheaf gluing versus ordinary evaluation of torsor-associated modules.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-module-is-sheaf: arbitrary site sheaf gluing versus proving an equivariant presheaf is a sheaf.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-equivariant-module-recover-linear: arbitrary site sheaf gluing versus recovering linear maps from equivariant data.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-graph-evaluation: arbitrary site sheaf gluing versus graph evaluation for torsor sections.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-section-evaluation: arbitrary site sheaf gluing versus torsor section evaluation.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-ordinary-evaluation-equivariant: arbitrary site sheaf gluing versus equivariant ordinary evaluation.
lem-weil-pbc-site-sheaf-gluing vs def-weil-pbc-torsor-associated-module: arbitrary site sheaf gluing versus the definition of a torsor-associated module.
lem-weil-pbc-site-sheaf-gluing vs lem-weil-pbc-torsor-normalized-graph-evaluation: arbitrary site sheaf gluing versus normalized graph evaluation.

## Second reading by NF

- Item statement: compared every hypothesis and conclusion with Stacks 04TR, sites.tex, label lemma-glue-sheaves (lines 5810–5888), and the module definition: covering pullbacks exist by the site axioms, equal indices and the triple cocycle are included, and the module assertion is the componentwise version of the source construction. Verdict: correct, unchanged; no statement dispute.
- Original step 1: compared with the new underlying-sheaf node's existence/overlap statement. Verdict: the citation was accurate, but its content is now proved directly in steps 1 and 3–6.
- Original step 2: compared with both definitions and the new node's statement. Verdict: repair required; existence of local identifications does not specify a construction by choosing a component, and the cited new node did not state the compatible-tuples formula.
- Original step 3: compared with the overlap equation of the new node. Verdict: correct conditional on a valid module construction; replaced by the explicit graph pullback calculation in step 6.
- Repaired step 1: checked against the compatible-tuples formula in 04TR and the cited site and localization definitions. Verdict: elementary restriction/naturality check; all fibre products justified by covering base change.
- Repaired step 2: checked against the cited module and localization definitions. Verdict: elementary componentwise module operations, scalar restrictions on overlaps, and semilinearity; no unstated theorem used.
- Repaired step 3: checked against the equalizer/sheaf axiom and covering base change in the cited site definition and the cited localization/module definitions. Verdict: one amalgamation in each local sheaf, one separatedness check on each overlap, and componentwise uniqueness prove the sheaf condition.
- Repaired step 4: checked against the cited localization/module definitions and the given (k,i,j) cocycle. Verdict: graph evaluation and the inverse tuple are explicitly typed on arbitrary slice objects, natural, and linear.
- Repaired step 5: checked against the cited definitions and the given (k,k,k) and (k,i) equations. Verdict: full-diagonal cancellation and pullback of the tuple equation prove both inverse identities; repeated-index overlaps are not silently identified with U_k.
- Repaired step 6: checked against the cited definitions and the pairwise tuple equation. Verdict: graph pullback gives exactly the requested overlap equation of module maps.
- New node lem-weil-pbc-site-sheaf-gluing: compared against 04TR, label lemma-glue-sheaves; correct hypotheses and conclusion, statement only, but localization notation lacked an inline definition citation despite its stmt_deps. Verdict: removed, since the source construction and all omitted checks fit the item's elementary steps; it creates no residual work item.

Changed: replaced the three-step existence/transport proof by six explicit compatible-tuples steps, removed the now-unneeded underlying-sheaf node, recomputed proof_deps and citations.json with verbatim definition clauses, and recorded three independent second-reader Mathlib searches as run. The first worker's Review by NF and other sections above are preserved as historical review of the original split.

Duplicate/source searches: read the existing open-cover module-gluing statement; it is restricted to a topological space. Searched every DAG chapter for 04TR and gluing/descent wording; the same-tag torsor nodes listed above have fixed torsor hypotheses and do not supply this general site assertion. blueprint_refs.py searches for “gluing sheaves” and “04TR” both returned zero blueprint matches. Independent LeanFinder search found the generic pseudofunctor descent equivalence, but its IsStack hypothesis is precisely effective descent, not a proved instance for module sheaves; Loogle found bottom-topology and dense-subsite equivalences, and grep found section-amalgamation and abstract descent infrastructure. Read their source signatures; no exact Mathlib leaf found. Name/concept searches in both read-only upstream source trees found no completed declaration of this item. The master Colimit/TwoColimit.lean (Obj) paragraph, lines 73–79, motivates gluing; constructibleCocone_essSurjObj at lines 237–238 is sorry and is not evidence of a finished proof. GOAL.md and coord/dag-sync.md were read; no Lean or build work performed.

Small cases: zero ring forces zero local modules and the compatible tuple module is zero; zero local sheaves give zero F; a field requires no extra hypothesis. For the identity one-object cover the cocycle forces the transition to be identity and graph evaluation recovers F_1. For a one-object nonmonomorphic cover, the graph/diagonal proof still applies and does not assume U_1 times_U U_1 = U_1. An empty covering, when allowed, remains empty under every base change, so F(V) is the singleton/zero module on every slice object and the sheaf axiom holds; this covers the empty scheme case. Empty index and repeated indices introduce no extra hypotheses.
