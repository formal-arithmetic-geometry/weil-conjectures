## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-nilpotent-ideal-flatness-criterion.json: statement node, split by exact application of the already reviewed live node lem-sfb-nilpotent-ideal-module-flatness; no Mathlib match.
- citations.json: the single proof citation, quoting the entire existing statement verbatim.
- report.md: this report. Existing searches.jsonl was read and retained; additional actual item searches were appended by msearch.py.

Attachments: none. Searches of lean/WeilConjectures by blueprint tag and by nilpotent flatness terminology found no project declaration proving this exact arbitrary-ring, arbitrary-module statement. The existing flat-Tor ideal criterion is a different theorem, not an attachment for this item.

WANTED: none.

What was wrong: the assigned unsplit node duplicates the already reviewed live node lem-sfb-nilpotent-ideal-module-flatness, accepted on 2026-10-23. Its reviewed record explicitly notes this duplicate. Their mathematical statements are identical after renaming I to J, including absence of Noetherian, finite-generation, and completeness assumptions. The assignment does not authorize editing the other node or its users, so the delivery reuses that existing node and flags this pair for maintainer reconciliation. No target statement is changed.

Unfinished: none within this item. Zero new nodes, zero new Mathlib leaves. The existing reused node has its own reviewed five-step Stacks proof and dependencies, which this delivery does not duplicate.

## Not duplicates

No new nodes are created. Pre-existing duplicate pair: lem-sfb-nilpotent-ideal-flatness-criterion vs lem-sfb-nilpotent-ideal-module-flatness: exactly the same statement, with I renamed J. This delivery cites the latter, already split and reviewed, rather than inventing a replacement lemma. Maintainer reconciliation of the two ids is requested.

## Review by Q124

I read Stacks algebra.tex, Tag 051C (lemma-what-does-it-mean), its statement and proof through the final nilpotent-ideal assertion, and Tag 00M6 (remark-Tor-ring-mod-ideal). The source first obtains Tor vanishing on R/I-modules from a free presentation and the quotient tensor comparison, then inducts on the annihilating power through IN and N/IN. The final flatness assertion applies to arbitrary modules because I is nilpotent. The injective multiplication hypothesis is the ideal-sequence form of the required Tor vanishing. Thus the imported item is true with exactly its current hypotheses.

For proof Step 1 I opened the full statement of lem-sfb-nilpotent-ideal-module-flatness and its reviewed proof, not merely its title or proof dependency list. Its statement introduces an arbitrary commutative R, a nilpotent ideal I with exponent n >= 1, an arbitrary R-module M, the generated submodule IM, flatness of M/IM over R/I, and injectivity of the very same multiplication map. Substituting I = J identifies every object, action and map. The cited sentence explicitly concludes that M is flat over R. The whole statement is quoted verbatim in citations.json. This is reuse of a pre-existing exact theorem, not displacement of the item into a new node. No uncited non-elementary inference is left in the one application step.

I checked the statement on J = 0 (the reduction hypothesis itself says M is flat), M = 0, the zero ring, and R = k[e]/(e^2), J = (e). In the last example M = R satisfies both hypotheses, whereas M = k has flat reduction but fails multiplication injectivity since J tensor_R k is nonzero and multiplication is zero. This verifies that the map hypothesis has not been silently omitted. No local, Noetherian, finite-generation or completeness hypothesis is used. The distinction between algebra flatness and module flatness introduces no new condition here.

I searched the whole DAG by tags 051C/00M6 and nilpotent-flatness language and ran blueprint_refs.py search for nilpotent and flatness, as well as ancestor for this item. The exact match is the existing created node above, not another imported blueprint node, so same_as remains empty. I read the current latest blueprint unit and direct-images proof. The inherited supporting deformation-algebra route is preserved; both nodes have the same unit. I checked the full dependency closure of the reused node: it has 40 nodes and does not contain this item, so this application creates no cycle.

I retained every imported item field and the existing Mathlib search records. The sandbox's earlier searches concern prospective Tor sublemmas; since the live exact duplicate supersedes the need for those new nodes, I did not create or misattribute them. The logged earlier item grep was reused and the actual item was searched with LeanFinder, Loogle and LeanSearch. Their hits are all-ideal flatness tests, not this single-nilpotent-ideal lifting result. No new Mathlib leaf is claimed. There is no statement dispute, no source error, no SGA citation, no new statement-only node to check, and no proof step longer than 2000 characters. I checked the delivery-errors B--E requirements against the node and sources: all new-node cases are avoided by reuse, the only citation says exactly what is used, and the hypotheses and maps agree clause by clause.
