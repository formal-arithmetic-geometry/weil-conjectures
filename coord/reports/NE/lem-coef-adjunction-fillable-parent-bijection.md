# Stage-1 report: lem-coef-adjunction-fillable-parent-bijection

## Files written

- `dag/nodes/sec-six-functors/lem-coef-adjunction-fillable-parent-bijection.json`: statement, now split in seven elementary coordinate steps using the existing normal-form theorem. No new nodes; zero Mathlib leaves.
- `citations.json`: one entry for each of the six step/node citation pairs, with an exact substring of the cited statement.
- `searches.jsonl`: six searches performed through the required launcher command. The scratch directory records the finite string verification and the JSON-writing script; these are sandbox artifacts.

## Attachments

None. Searched all of `WeilConjectures/` in the read-only slopmaster2 source by the exact blueprint tag, fillable, squiggle, parental, walking-adjunction and free-adjunction concepts. The free/forgetful adjunctions found there concern modules and iso-algebras and do not give any clause of this item. No compiler or Lake command was run. Master source sorry declarations were not treated as finished proofs.

## WANTED

WANTED: Emily Riehl and Dominic Verity, *Homotopy coherent adjunctions and the formal theory of monads*, Advances in Mathematics 286 (2016), pp. 832–834, Section 4.1 and Definition 4.2.1, archival copy for this item. Read [the authors' PDF](https://emilyriehl.github.io/files/adjunctions.pdf) online. No local copy appears in the literature inventory or file search. The proof is marked agent-written, and is an explicit calculation from the existing normal-form statement rather than an unsupported appeal to the online lemmas. No Stacks tag states this specialized combinatorial result.

## Corrections and source comparison

The statement is unchanged. The formerly empty proof is replaced by seven steps. The terminal `+` in the first parent formula must move from integer code r+1 to r+2, whereas the initial `+` in the second case is replaced by the new internal level r+1; the proof states these operations separately. These are clarifications already consistent with the item, not statement repairs.

The nearest blueprint ancestor is `prop-coef-integral-exceptional-adjoint`, proof paragraph 2, finite enriched mapping-complex adjunction before the inverse limit. I read the ancestor, chapter record, and unit record. The cell-filtration intermediate ancestry is retained. The split stays below that unit; its sole dependency has the same unit. No chapter or unit metadata was changed and no off-route tool use was introduced.

## Unfinished work

None in this one-level split. The existing normal-form theorem remains its own separate item. This delivery does not purport to prove that theorem.

## Search and duplicate checks

Whole-DAG searches for fillable, squiggle, parental, the cited lemma numbers and the source identify the existing normal-form, nondistinguished-face-rank and cell-filtration nodes. The rank and cell-filtration nodes depend on this item, so neither is used here. Blueprint reference searches for fillable and squiggle returned no imported blueprint nodes; the broader adjunction search also provided no statement of this atomic matching. The ancestry query confirms the existing ancestor and via chain.

Fresh searches for this item used leanfinder (two different semantic phrasings), loogle (two patterns), leansearch and grep, with the exact queries and output digests retained. The first results concern arbitrary simplicial horns, skeleton/coskeleton and nerve adjunctions. The second semantic results concern free-group word reduction and a free monoidal category; the other Loogle results are free/forgetful adjunctions for modules, groupoids and condensed objects. Their printed types do not concern the free strict adjunction's atoms or this matching. The source grep had no hits. No candidate is an exact match or one-line specialization, so this is not a Mathlib leaf. Old searches imported with the node were replaced by the actual searches for this item in this sandbox.

## Not duplicates

No new nodes were created. The existing normal-form theorem provides coordinates, not the matching; the cell-filtration theorem and face-rank theorem use the matching. Nothing is renamed or moved into a new statement-only node.

## Review by NE

I read Riehl–Verity Definition 4.1.1, Observation 4.1.2, Lemmas 4.1.3–4.1.4 and Definition 4.2.1 online, and read the entire statement of `lem-coef-adjunction-squiggle-normal-form` in the DAG. There are no new-node sources to review. The cited normal-form statement explicitly supplies the alphabet, strict inequalities, nondegeneracy criterion, atomicity criterion, face map and concatenation formula; I did not take any facts from its proof. All six citation records are verbatim substrings of that statement.

Step 1 uses its atomicity and nondegeneracy criteria: without internal endpoints degree-zero atoms have width one, and positive degree forces an internal level. This verifies the exceptional degree-zero case and the bounds on depth. Step 2 uses its actual face formula: the sole k can have no adjacent k+1, so no reduction occurs, and the occurrence of old k+1 gives the repeated new k. The assumptions k<n and nondegeneracy are both used; no face theorem or general horn theorem is hidden here. Step 3 uses that face formula and concatenation: only the first interior letter becomes an endpoint; deleting the fixed initial minus produces the claimed atom, and preserves all lower levels. It explicitly includes n=1 and the width drop, so the candidate child is a genuine nonidentity atom even at the boundary.

Step 4 uses precisely the same atomicity and nondegeneracy tests on the displayed parent. The assumption that b is nonfillable with target minus supplies a second occurrence of b1; it is essential to make the new level j+1 occur. Strictly increasing relabeling handles all other comparisons, while the first comparison is checked separately. Step 5 uses the same tests and the face/concatenation formulas with target plus. I checked w=1 separately: then nondegeneracy forces r=0 and b=u; otherwise b1 is an internal numerical letter. These checks rule out confusing an endpoint with a numerical level. Step 6 uses only the face formula and the preceding computations to force each preimage; fillability distinguishes the two possible preimages of j, and atomicity distinguishes the internal top level from a terminal plus. Thus uniqueness is proved, not quoted from a new node restating the conclusion. Step 7 uses the preceding existence and uniqueness arguments to write both inverse equations and needs no further external fact.

For the B–E checklist: statements and hypothesis scopes are self-contained; no source metadata or other protected fields were changed; there are no unsplit new nodes carrying proofs, duplicate nodes, clause-as-node substitutions, or unsupported tag citations. Every imported non-elementary fact used is exactly a clause of the cited normal-form statement (C1/C4); each remaining calculation is a direct finite-letter argument from that clause. The dependency list is the union of the actual citations, and no descendant is cited. There is no transport, implicit comparison, existence choice or auxiliary theorem hidden in a long step: every step is shorter than 1000 characters.

I tested small cases with a standalone Python enumeration of all nondegenerate atomic strings of dimensions 0 through 4 and widths 1 through 7: 300 strings, of which 55 are fillable and 245 are nonfillable. It checked both inverse equations, atomicity and nondegeneracy of the output, the absence of reduction in distinguished faces, and both width cases, including parents in degree 5 / width 8. In particular u has parent epsilon and eta has parent beta with the new terminal code. This is an edge-case check of the stated coordinate constructions, not a Lean proof or a substitute for the written argument. No discrepancy requiring STATEMENT-DISPUTED was found.
