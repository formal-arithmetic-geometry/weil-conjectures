## Files written

- `dag/nodes/sec-six-functors/lem-coef-poset-relative-vertex-insertion.json`: existing statement node, split; statement unchanged; no new nodes and no Mathlib leaves.
- `citations.json`: verbatim statement quotations for every step and every cited node.
- `searches.jsonl`: actual additional Mathlib search results from the prescribed command; the original five valid item-search records remain in the item.

## Attachments

None. Rechecked the read-only slopmaster2 `WeilConjectures/` tree for the item id, relative vertex insertion, initial-poset slice terms, and poset/vertex terminology. No declaration states the item exactly. The shared item has no Lean attachment. Upstream sorry declarations are not treated as proofs.

## WANTED

WANTED: archived HTT, Proposition 5.3.5.15, proof (a)-(b), printed pp.410–411 (PDF pp.427–428), for this item's finite-poset insertion and comma variation. Read the online PDF at https://people.math.harvard.edu/~lurie/papers/HTT.pdf without downloading it; proof_origin remains agent. No Stacks tag states this quasicategorical result.

## What was wrong and what changed

The retained item and report were present, so I first ran the required dry run. It completed with `OK (not pushed)` at f7d1bcdff3. That mechanical success did not settle the mathematics. The retained proof lifted only the new vertex to the upper join slice, then claimed that a fixed-boundary join/cone equivalence glued the result. That equivalence does not itself prescribe all existing mixed lower/upper simplices. I replaced this with an application of the existing least-vertex restriction theorem to the entire cone, relative to the entire lower diagram. This fixes precisely the missing boundary data.

The split now has five steps: identify both links and the original map to the upper join slice; glue the distinguished incoming cone to the evaluated lower diagram as a simplicial pushout and check its size; apply filteredness; lift the full lower cocone relative to its boundary; unpack the join slice and glue maps along an explicitly equal intersection. The argument uses neither a colimit nor compactness nor local smallness.

I also removed two unrelated constructible-pullback statement dependencies and four unrelated constructibility searches from the retained sandbox copy. They are absent from the current shared item, occur nowhere in its statement, and are not searches for this lemma. The original five relevant item searches and their actual results are retained. Additional searches used two natural-language formulations, Loogle, grep, and LeanSearch. Read the returned ordinary successor-extension and filtered-category results, and the inner-horn filler: they do not state this quasicategorical relative extension. The invalid unquoted Loogle query is expressly recorded as invalid, followed by a valid quoted query. No search was invented.

The item statement agrees verbatim with the current shared item. There is no statement dispute. The current blueprint ancestor and its derived-adjunction paragraph were read; this is inherited auxiliary Ind infrastructure, not a claim literally written in that paragraph. No chapter or unit route is changed. Whole-blueprint searches for vertex insertion and prescribed incoming data found no equivalent blueprint node. No new node is proposed.

## What could not be finished

Nothing in the requested stage-1 split remains unfinished. The HTT archival request remains WANTED; no Lean was written or compiled.

## Review by Q95

I read delivery-errors B–E in full, the chapter and unit records, the current ancestor proof, the shared item and retained files, the online HTT proof (a)-(b), and the full statements of the cited slice, filteredness-definition, and least-vertex restriction nodes. The HTT induction inserts a vertex using its lower link and the slice over its upper link; its comma variation requires the incoming-arrow data retained here. The general hypotheses of the item suffice: the upper link has a least element independently of any ambient colimits, and filteredness is assumed exactly for the evaluated restricted slice R.

Step 1 uses only the explicit join and join-slice construction of lem-coef-infinity-slice-right-fibration. The proof spells out the correspondence degreewise instead of citing the node's unrelated Kan-fiber clause. Minimality outside the order ideal gives every strict predecessor in L, and the product order makes every lower vertex less than every upper vertex. Fullness ensures the whole source face lands in E0, not just its vertices. Thus U really gives a map h into the upper slice S and rh is the specified evaluated lower diagram.

Step 2 uses def-coef-presentable-infinity-category for its precise nondegenerate-simplex cardinal convention. The pushout and its map are defined degreewise along inclusions; no assertion that an arbitrary nerve preserves a poset pushout is needed. The cardinal count covers finite kappa-small sets when kappa is aleph_0 and countable unions of finite-chain sets when kappa is uncountable regular. All sets stay in the stated small universe.

Step 3 uses the filteredness clause of the same definition node for the small simplicial set K. It first supplies a coherent cocone in the comma convention. The existing lem-coef-join-slice-cocone-comparison then supplies a vertex of the sharp join slice for the fixed diagram w. A quasi-inverse to that equivalence produces a map on K joined with a final vertex whose restriction is exactly w, by the definition of this join slice. Both prescribed factors are consequently preserved exactly. This comparison was missing from the retained proof and is now cited explicitly; no colimit hypothesis is needed.

Step 4 uses precisely the whole-boundary lifting clause of lem-coef-initial-poset-slice-restriction, applied to N(M) included in its right cone. Its hypotheses hold: T is small with least element a, E is a quasicategory, E0 is full, and p is the restriction of F. The commutative square is checked explicitly, rh = v = c restricted to N(M). This is the substantial cited theorem; lifting just an object would have been insufficient.

Step 5 uses the join-slice definition again. Concatenating the three ordered blocks identifies every new simplex, and their intersection with the old complex is exactly the old lower/upper join. Maps agree there by the relative lift, so ordinary degreewise gluing gives U'. The equality rH=c proves that the row agrees with beta' on its entire simplicial boundary. These are elementary consequences of the constructed maps, with the details written out rather than hidden under a comparison theorem. No homotopy equivalence is used to assert strict equality.

I tested empty B, empty M, a one-element A, incomparable elements of L, and kappa=aleph_0. Incomparable elements of L are correctly excluded from the lower link. Empty joins still give the required new vertex and the incoming edge from d; finite nerves have bounded nondegenerate chain length. All five steps are below 2000 characters. Every non-elementary input is a cited statement, and quotations in citations.json were checked against the current statements. No new node means there are no duplicates, unsplit-node proofs, or new-node edge cases to audit. The retained proof/report were repaired on the substantive boundary issue despite their initial dry run passing.

Continuation after the interrupted worker: the required initial dry run exited successfully at c6a65a053c before any edit. I compared every item field with the current shared node: its statement, statement dependencies, chapter, unit, and blueprint ancestry already agree; the shared node is still unsplit. I reread the retained search log and the actual ordinary-category successor-extension/filtered-cocone and inner-horn hits. They do not prove this relative quasicategorical statement, so no search was repeated or invented. A fresh project-source search found no item-tag or relative-insertion attachment. I read the current ancestor proof's derived coefficient adjunction paragraph and kept its supporting-infrastructure ancestry.

The mathematical continuation corrected one additional C1 gap: the definition node's coherent cocones use the comma convention, whereas the subsequent lifting square uses a sharp join. I read the full statement of lem-coef-join-slice-cocone-comparison and HTT Proposition 4.2.1.5 and Corollary 4.2.1.7 online (printed pp.241–242). Its functor equivalence is for the fixed boundary diagram w, so applying a quasi-inverse supplies a sharp join object with that boundary exactly, even though its comparison cocone need only be equivalent to the selected comma cocone. No preselected cocone needs preserving. This node is in the same unit and its dependency closure does not reach this item. Step 3 is now non-elementary and cites it, with a verbatim statement quote in citations.json. No statement was changed, and no new node or Mathlib leaf was added.

WANTED: archive HTT Proposition 4.2.1.5 and Corollary 4.2.1.7, printed pp.241–242, for the additional existing comparison used by step 3. Online source read without downloading. I also rechecked empty B, minimal a with empty lower link, and singleton A: the pushout K still contains the prescribed d vertex and its cone supplies the required edge; all join inclusions and boundary lifts retain their meaning. The cardinal count uses finite nondegenerate nerves for kappa=aleph_0, and regularity for the countable union when kappa is uncountable. All five steps remain under 2000 characters.
