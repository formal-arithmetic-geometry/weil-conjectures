# Stage-1 worker report

## Worker report

### Files written

- `dag/nodes/sec-six-functors/lem-coef-free-factor-hammock-universal-cover-reduction.json`: split statement, eight proof steps; no Mathlib match.
- `citations.json`: eight entries, with verbatim statements for all step/node pairs.
- `searches.jsonl`: actual `msearch.py` records, including five distinct queries in this reading.
- `revise_split.py`: sandbox-only editing script; not a delivery node.

There are **0 new nodes and 0 Mathlib leaves**. I removed the earlier sandbox-only files `lem-coef-free-category-universal-cover-graph.json` and `lem-coef-free-category-tree-nerve-contractible.json` before delivery preparation. They were never repository nodes. The current proof constructs the covering graph directly and reuses `lem-coef-free-category-groupoid-nerve` instead of introducing a tree-nerve clause node.

### Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the full item id, hammock, universal-cover and oriented-tree language, and free-category nerve language. The only universal-cover hit concerned Artin–Schreier, which does not state any clause of this item. The master checkout is reference only; its sorry declarations are not evidence of completion.

### WANTED

WANTED: local literature mirror of Dwyer–Kan, *Calculating simplicial localizations*, Comparison Lemma 2.3 and Section 5.8(ii), printed pp.20,25, for lem-coef-free-factor-hammock-universal-cover-reduction. The source is available online at the URL already recorded by the item and was read online; no file was downloaded or written outside this sandbox. I marked the explicit expansion `proof_origin.by = agent`, since the local literature has no copy and the source leaves the rectangle-lifting details implicit.

### Problems corrected

The item's statement is unchanged. The earlier attempt had not completed its required dry run. Its proposed graph-cover node included the free-category cover clause itself; its tree-nerve node was exactly another clause. I replaced both by the reduced-word construction within the proof and the existing general free-category/groupoid-nerve theorem. This is an argument for the item rather than a relabeling of its conclusions.

The earlier report claimed the source and searches had been checked, but the node search summaries did not accurately reflect all successful LeanSearch records in `searches.jsonl`. Those two node files have been removed. I preserved the repository item's historical searches and appended the five distinct queries actually run in this reading, with the complete log records and digests. All services succeeded for these five distinct queries. `CategoryTheory.Paths.lift` and `lift_unique` give extension of a graph map to a functor, not lifting of arbitrary hammocks to a connected tree cover. The Cech nerve and `classifyingSpaceUniversalCover` hits describe EG, not a free-category cover with the stated coproduct. I read the matching source passages in PathCategory/Basic.lean, CechNerve.lean and RepresentationTheory/Homological/Resolution.lean. Nothing supplies the item as an exact or one-line Mathlib specialization.

### Unfinished work

No mathematics is deferred to a new node in this delivery. Existing dependencies remain their own stage-1 tasks. The server review check passed; the required packaging gate is documented below, and READY is returned only after its OK result. No push is authorized in this first-reader turn; the second reader delivers.

## Blueprint and duplicate searches

I read the chapter and `sk-prop-sf-biduality-general` unit records. I read both the master ancestor and the current `main-20261015` statement/proof at `sec-six-functors/sk-thm-sf-package/prop-coef-integral-exceptional-adjoint`. The paragraph beginning “For K” and its derived coefficient-adjunction display are the historical ancestry of this mapping-space foundation. This item remains specifically the universal-cover reduction after W=C and restriction to a connected component; it changes neither the coefficient adjunction nor the unit/chapter route.

`tools/blueprint_refs.py ancestor` returns `prop-coef-integral-exceptional-adjoint`. Whole-blueprint searches for `free category`, `universal cover`, `tree`, `groupoid` and `contractib` yielded no blueprint node equivalent to this item. The DAG search for universal-cover, free-category/nerve, covering-tree and oriented-tree language found the existing `lem-coef-free-category-groupoid-nerve`, which supplies the general weak-equivalence theorem used in step 4. I also opened the full statements of the hammock-graph presentation, nerve-natural-homotopy theorem, realization simplex/topology lemma and Whitehead lemma. No new node remains to compare for duplicate tags.

## Not duplicates

No new nodes remain. The existing groupoid-nerve theorem is reused, not copied. The item itself is unchanged in statement and cannot be replaced by that theorem, which says nothing about covering graphs or hammock mapping sets.

## Review by Q75

I read Dwyer–Kan's *Calculating simplicial localizations* online, Definition 2.1 (printed p.19) and Section 5.8(i)–(ii) (printed p.25). The latter first reduces to W=C and connected nerve, then uses the universal cover to reduce to contractible nerve. I checked that our statement is restricted to exactly that situation and asserts no complementary factor and no connected cover of a disconnected category. The explicit signed-word and hammock argument is my expansion of that reduction. I also read *Simplicial localizations of categories*, Sections 2.8–2.9 (printed p.271), alongside the existing groupoid-nerve node's general statement and proof. There is no relevant Stacks tag and no SGA source is used.

Step 1 is an explicit stack reduction algorithm on signed edge words. I checked its delicate cancellation case: when appending a letter erases the last letter, appending its inverse restores that letter, since the previous word was reduced. Insertion/deletion of adjacent inverse letters therefore preserves the output in any suffix context. This establishes the reduction identity needed later without assuming a groupoid normal-form theorem. Formal inverse letters are distinct even for a loop, so an edge is never accidentally made involutive.

Step 2 constructs the graph, with one edge for a vertex and an outgoing positive generator, and proves the tree property from word length. A nonempty reduced word has a unique shorter neighbor, its prefix; all other neighbors are longer. Thus a maximal-length vertex in a finite cycle would have two shorter incident edges, impossible. Every vertex joins the empty word by prefixes. Smallness follows from finite words in the small generating graph. These are elementary arguments from the displayed construction, not an uncited existence theorem for covering spaces.

Step 3 verifies the cover and extends to free categories by words. For a negative letter the lifted positive edge starts at red(w e^-1) and ends at w; this checks both incoming and outgoing generators. Unique arrow lifting follows by induction on positive word length, and lifting backward gives the prescribed-target version. Connectedness is used only for object-surjectivity; nonemptiness was used for v_0. Projection preserves positive word length, which is the additional fact needed to reflect identities in step 7. No topological covering theorem is assumed.

Step 4 uses exactly the statement of `lem-coef-free-category-groupoid-nerve`: its canonical NP(Q) to NG(P(Q)) is a weak homotopy equivalence for a small graph, including loops and isolated vertices. Our graph is small and its category is free. I wrote the signed-word presentation of its groupoid completion and why tree walks reduce to the unique simple path; this makes G indiscrete, with the empty-word vertex terminal. The cited `lem-coef-nerve-natural-homotopy-equivalence` states that a natural transformation yields a continuous homotopy of realized nerves, with no invertibility requirement. The unique arrows to the root provide exactly the natural transformation it requires; the other composite on the one-object category is the identity. Its conclusion contracts |NG|.

Step 5 treats actual contractibility of realization explicitly. `lem-cbc-realization-cw-subcomplex` states unique nondegenerate representatives, factorization of degenerate simplices, face-identification relations, and the final closed-set criterion. I used precisely these facts to exhibit one CW cell for each nondegenerate simplex, finite face closure, and the weak topology. Euclidean simplices are disks with spherical boundary. `lem-cbc-whitehead-cw-homotopy-inverse` then applies to the canonical realization map: both source and target have the described CW structures, and the weak-equivalence conclusion of the groupoid-nerve node supplies every component and based-homotopy-group hypothesis. This avoids silently identifying “weakly contractible” with “contractible.” These two CBC nodes are generic tools, declared in `split_report.tool_uses`; they replace no unit proof step. Their statements, rather than their internal proofs, are the interfaces used.

Step 6 cites the complete rectangle description from `lem-coef-hammock-graph-colimit-presentation`: finitely many rows/columns, downward arrows, and identity endpoint arrows. It does not take a lifting theorem from that node. Lifting is proved using steps 1–3. For a rightward square the positive-word equality is ad=bc; for a leftward square, with a from upper-right to upper-left and c from lower-right to lower-left, it is ab=dc. I checked these domains carefully. Equal words have the same lift with the same initial vertex, giving equality of arrows, not merely equality of endpoints. Unique target lifting handles the leftward direction. Identity endpoint arrows force the same lifted endpoints in every row. All arrows are permitted because both distinguished subcategories are the full categories.

Step 7 uses exactly the hammock node's deletion/composition reduction operations. Reflection of identities from step 3 proves that projection of a reduced diagram stays reduced; lifting alone would not suffice for this assertion. Positive-word concatenation proves that lifts of composites are composites of lifts. Identity-column deletion therefore identifies equal lifted vertices, and these operations preserve endpoints. This is elementary after steps 1–3 and the cited definition of reduction.

Step 8 uses exactly the cited row-deletion/repetition and subsequent-reduction operations. The uniqueness induction fixes the top row, each vertical arrow and each next row. Row deletion composes vertical arrows, repetition inserts identities, and step 7 handles ensuing horizontal reduction. I checked that target lifts are preserved by these operators, so the maps really have a fixed coproduct summand. The length-zero diagram when x=y lifts only to the target equal to the chosen source lift. Projection/lifting are therefore inverse simplicial maps, not only bijections of vertices or homotopy equivalences.

For the edge cases I checked a single vertex with no generators (one lifted vertex and only length-zero hammocks), one directed edge with either orientation, one loop (distinct signed letters give the integer-line cover), two parallel generators (they stay distinct and produce no parallel edge in the tree cover), and arbitrary infinite connected graphs (all constructions and every hammock use finite words; no local finiteness or finite-generation assumption entered). A disconnected or empty graph is outside the item's stated hypotheses, rather than silently discarded during the proof. I also traversed each reused dependency's statement/proof closure read-only: none reaches this item, so these citations introduce no circular route.

The corrections from the previous sandbox attempt are removal of both clause-level nodes, restoration of the item's repository provenance fields, explicit identity reflection, explicit leftward-square handling, use of the existing general groupoid theorem, and a separate Whitehead step for actual realization contractibility. The exact statement is retained.

## Verification

Server `review_split` returned **PASS; 0 new nodes** for this split. It accepted both declared CBC tool uses.

Final packaging command: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q75 lem-coef-free-factor-hammock-universal-cover-reduction --no-push`. This runs the maintainer's preflight, including DAG and split checks, on the server. The worker's READY response is conditional on that command printing OK; no push is performed. This report is finalized before that packaging command copies it into the reviewable commit.

## Second reading by Q75

- Item statement: checked against Dwyer–Kan, *Calculating simplicial localizations*, Comparison Lemma 2.3 and §5.8(ii), pp. 20, 24–25; the connected nonempty free-category hypotheses, universal-cover tree, nerve contractibility, and hammock coproduct are all retained. Verdict: PASS.
- Step 1: checked signed-word reduction and adjacent inverse cancellation, including loops and endpoint preservation; verdict: PASS and elementary.
- Step 2: checked the reduced-walk graph against the universal-cover construction, uniqueness of the shorter neighbor, connectedness, acyclicity, and smallness; verdict: PASS and elementary.
- Step 3: checked positive and negative edge lifting, source/target uniqueness, object surjectivity, free-category extension, and identity reflection; verdict: PASS and elementary.
- Step 4: checked the groupoid-completion comparison against `lem-coef-free-category-groupoid-nerve` and the contraction via `lem-coef-nerve-natural-homotopy-equivalence`; verdict: PASS.
- Step 5: checked the realization CW argument against `lem-cbc-realization-cw-subcomplex`, Whitehead hypotheses against `lem-cbc-whitehead-cw-homotopy-inverse`, and the weak-equivalence input; verdict: PASS.
- Step 6: checked rightward and leftward rectangle equations, prescribed-source/target lifts, and endpoint identities against `lem-coef-hammock-graph-colimit-presentation`; verdict: PASS.
- Step 7: checked identity reflection, composition of lifted words, reduction operations, and endpoint preservation against the hammock presentation; verdict: PASS and elementary.
- Step 8: checked projection/lifting inverses degreewise and compatibility with faces, degeneracies, reduction, and the length-zero hammock; verdict: PASS and elementary.
- New nodes: none; there were no new-node statements to audit, and no Mathlib leaves. Existing dependency statements were opened and match their uses.

Changes made: corrected the node's `created.item` provenance from the parent comparison item to this delivered item; appended this second-reading audit. No mathematical statement or proof step required correction.
