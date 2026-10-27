# Q127 stage-1 report

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-morphism-cotangent-isomorphism-etale.json: statement item, split by specialization of an existing more general DAG node; Mathlib verdict no match.
- citations.json: one verbatim statement quotation for the single proof citation.
- report.md: this report. No new nodes or Mathlib leaves.

## Attachments
None. Searches of lean/WeilConjectures for the exact blueprint tag and for cotangent, differential and etale terminology did not find a declaration proving the item.

## Wanted literature
WANTED: literature/bosch-lutkebohmert-raynaud-neron-models.pdf, BLR 2.2 Proposition 8 and Corollary 10, printed pp.40–41, for lem-sfb-smooth-morphism-cotangent-isomorphism-etale. The primary scan was read through the web reader at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf (zero-based page 47 / PDF page 48). No file was downloaded. The agent-marked proof is the direct specialization of the existing DAG statement.

## Findings and changes
The item overlaps the already existing lem-sfb-smooth-cotangent-etale-criterion. That node's first clause is exactly this item, with further global and equal-rank determinant consequences. The brief expressly requires reusing an existing more general node; I therefore cite it and create no new copy. This leaves the actual criterion proof on the existing unsplit node, where it belongs. The maintainer may eventually merge these overlapping nodes; I have not changed the other node or the item's maintainer-owned fields.

No statement dispute or change is needed. The source scan puts Corollary 10 at printed page 41, PDF page 48 (zero-based 47). Source fields are retained. The inherited blueprint.from.node is null; blueprint_refs.py ancestor confirms that no blueprint ancestor is recorded, so I retained the ancestry and filled the split report with its actual supporting step. Searches of the latest blueprint and blueprint_refs.py by cotangent, differential and etale found no blueprint node stating the whole criterion. No unit binding fields are changed: this is not a unit key node.

## Not duplicates
No new nodes. The existing item is the pointwise clause of lem-sfb-smooth-cotangent-etale-criterion, which additionally states the global sheaf and determinant consequences. This delivery reuses that existing statement instead of introducing another duplicate.

## Review by Q127
I read the full item, its chapter and unit records, the stage-1 contract, GOAL.md and the three-level route rules, and both B–E sets in delivery-errors.md. I read the full statement of lem-sfb-smooth-cotangent-etale-criterion. For step 1, its first sentence introduces arbitrary schemes over an arbitrary base, both structural morphisms smooth, and an S-morphism h. Substituting h=g is legitimate precisely because qg=p. The differential maps agree by the displayed formula on a tensor generator, which determines a linear map; the target definition of relative differential sheaves and tensor pullback has the same meaning in both nodes. The cited pointwise equivalence is quoted verbatim in citations.json. Its extra same-rank condition modifies only the later determinant clause; it does not constrain the clause being used. Thus no Noetherian, field, separatedness or pure-dimension condition is imported. This is an application of an existing more general statement, not a new lemma restating a clause.

For source verification I read Corollary 10 in the primary BLR scan: it assumes smoothness of X/S at x and Y/S at g(x), and equates etaleness there with bijectivity of precisely the pulled-back differential stalk map. Global smoothness in the item implies these local assumptions. I also read Stacks morphisms.tex Tag 02GU (lemma-etale-at-point), including its square-Jacobian condition, but do not cite a Stacks tag as a substitute for a DAG fact. No SGA source is used. The only cited node is in the same unit and has empty proof and statement dependencies excluding the item, so this edge cannot create a cycle.

I checked small cases: the identity map gives the identity differential; a map between etale S-schemes gives the unique isomorphism of zero differential modules; the empty source has no points and is vacuous; ranks may vary on different components because no determinant clause is used; the p-power endomorphism of the affine line over F_p has zero differential and is not etale, consistent with the criterion. The base can have nilpotents: the cited statement and source impose no reducedness. There is no long step (the single application is below 2000 characters), no new unsplit node carrying proof text, no hidden flatness deduction, and no informal replacement of an actual comparison map.

For the Mathlib audit I read the actual msearch results and the current Etale.lean source. The returned etale definitions, smoothness instance, etale locus and cancellation lemma neither express nor imply this whole differential equivalence in one specialization. The grep result is an import, not a matching theorem. The earlier item's recorded second semantic phrasing also returned only those general notions; its searches and results are preserved. Current searches are appended from the actual sandbox searches.jsonl, with exact query text. No unavailable result is described as a negative hit.

## Unfinished work
None for this one-level split. The reused criterion remains an existing stage-1 item; this delivery does not claim its Lean proof or its own Mathlib leaf.
