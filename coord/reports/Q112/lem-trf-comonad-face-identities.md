# Stage-1 report: lem-trf-comonad-face-identities

1. Files written: dag/nodes/sec-trace-formula/lem-trf-comonad-face-identities.json (statement, split; no exact Mathlib match), citations.json, and this report. searches.jsonl is the unmodified search-command log. No new nodes or Mathlib leaves.
2. Attachments: none. Searches of lean/WeilConjectures for the blueprint tag and comonad, Godement, face/counit terminology found no declaration giving all clauses.
3. WANTED: none.
4. The imported statement is correct and unchanged. Its empty proof is replaced by a componentwise expansion of Stacks' argument. The source does not require a comultiplication for this clause. All original searches, provenance and blueprint fields are retained; the new logged searches are appended. No unit or chapter is changed.
5. Unfinished work: none in this one-level split. Existing dependencies remain with their current live status.

## Sources and route

Read GOAL.md, SETUP.md's three levels, coord/brief-stage1.md, stages/1-dag.md, roles/worker.md, tools/README.md, coord/STATE.md and delivery-errors B--E (including the merged copy). Read the chapter and sk-i-curve-zero unit records, and the current blueprint/latest chapter, unit and lem-trf-local-term-locality proof. This foundational category calculation serves the already recorded standard-resolution branch; it changes no chapter or unit route. No released repair note exists for the item.

For the item read literature/stacks-project/simplicial.tex, Example 0G5M (example-godement) and Lemma 0G5N (lemma-godement), opening and condition (1)(a). Read categories.tex's horizontal-composition definition and Lemma 003F (lemma-properties-2-cat-cats), including its naturality explanation. The Stacks interchange calculation is expanded directly into component naturality, so no separate interchange result is invoked without a node. No SGA source is used.

## Searches and reuse

The sandbox initially had no item, report, citations or search log. Read the live item's six inherited search records before running fresh queries. The required msearch commands produced five additional records (LeanFinder with two phrasings, Loogle, grep, LeanSearch), all available. Read Mathlib/CategoryTheory/Functor/Category.lean:116--147: hcomp and exchange are general calculus, not the full indexed statement. SimplicialObject face identities require a simplicial object already supplied; using them here would be circular. Comonad.counit_naturality requires extra comonad structure absent from the item. Neither gives an attachment or full-item Mathlib leaf. The proof instead uses the naturality already assumed in the statement.

Searched the whole DAG for 0G5N, 003F, horizontal composition, interchange, exchange, whiskering, and endofunctor powers. Read the existing def-trf-endofunctor-powers statement in full. The other comonad nodes are distinct simplicial clauses, and the enriched-category hits concern different objects. Ran blueprint_refs searches for horizontal composition, face identities and counit and the ancestor lookup. No equivalent blueprint statement was found; same_as remains empty. No new lemma is needed: the component evaluations and single application of the naturality axiom are written out rather than made into duplicate or elementary nodes.

## Not duplicates

No new nodes; no new/existing pair to distinguish.

## Review by Q112

I checked the statement against Stacks 0G5N (1)(a): the input is only an endofunctor with a natural transformation to identity, and both composites delete distinct positions. I kept the exact statement, including the common horizontal expression and naturality clause. I checked the horizontal convention in the item against the definition in categories.tex; it is the outer transformation evaluated on the new inner object followed by the old outer functor applied to the inner component.

Step 1 cites only def-trf-endofunctor-powers. Its statement really gives zero as identity and successor as composition, which proves the displayed power addition formulas by the written induction. Substitution in the definition gives each face component. The naturality equation is obtained from e's naturality at T^(n-i)(f) by applying T^i, so both its source T^(n+1) and target T^n are correct. No existence theorem or interchange lemma is silently used.

Step 2 cites the same definition for the iterates. I checked a=i, b=j-i-1, c=n+1-j are nonnegative and sum to n. With y=T^c(x), the map f=T^b(e_y) has source T^(b+1)y and target T^b y. The first composite is T^a(e_(T^b y) composed with T^(b+1)(e_y)); the second is T^a(T^b(e_y) composed with e_(T^(b+1)y)). These are exactly the two sides of naturality of e at f. Functoriality justifies combining their outside T^a maps. Equality of natural transformations means equality of all their components; no additional categorical theorem is needed.

Step 3 again cites the power definition, and expands the horizontal expression using the formula already in the item. Its component is exactly the first expression in step 2, not merely a map with the same source and target. I checked adjacent faces b=0, outer endpoint a=0, right endpoint c=0, all three possibilities at n=1, the empty category (all component assertions vacuous), and T=identity (all faces e, hence composites e composed with e). No inverse, comultiplication or counit equation is used. All indices and both equalities survive these tests.

Each citation quote in citations.json is a verbatim sentence in the cited definition's statement and supplies exactly the recursion used. I checked C1/C4 by reading that statement, rather than its proof or Lean record. All three proof steps are elementary component calculations, each under 2000 characters; there is no hidden standard sublemma with new hypotheses. No new node needs a source, search verdict or hypothesis audit. The report and node do not change any maintainer field. The required server preflight and dry run follow this review.
