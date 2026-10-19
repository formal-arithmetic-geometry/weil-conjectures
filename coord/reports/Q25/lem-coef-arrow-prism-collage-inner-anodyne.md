# Q25: lem-coef-arrow-prism-collage-inner-anodyne — repair

## Files written

- `dag/nodes/sec-six-functors/lem-coef-arrow-prism-collage-inner-anodyne.json`: restored the current repository's arrow-prism collage statement verbatim; supplied a nine-step relative inner-horn proof, status `split`. No exact Mathlib match.
- `citations.json`: 17 step-specific, verbatim excerpts, covering every citation in every step.
- `searches.jsonl`: retained the previous log, including the historical pullback searches, and appended one focused simplicial-set grep. All 13 relevant inherited searches remain in the node; the new grep is the fourteenth entry. The unrelated pullback searches are historical log entries, not evidence for the restored statement.

There are **0 new nodes and 0 new Mathlib leaves**. The existing Mathlib leaf `lem-weil-pbc-simplicial-set-nondegenerate-decomposition` supplies the unique nondegenerate decomposition. Sandbox-only `repair-history/` preserves the returned node, report, and citations; `check_staircase.py` checks the finite chains. No project, Lean source, launcher, chapter, unit, or citer file was written.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the exact id, arrow-prism/prism-collage wording, `collage`, `relativeJoin`, and inner-anodyne terminology found no project declaration stating the item. The existing stage-2 statement of the citer is not a closed proof of this item. Upstream master sorry declarations were not used as evidence of completion.

## WANTED

WANTED: archival copy of Kerodon, Proposition 7.3.5.5 (identifier 0302), construction of S, for `lem-coef-arrow-prism-collage-inner-anodyne`. I read https://kerodon.net/tag/0302 online; there is no Kerodon archive in this repository's literature directory. The stronger relative collage statement is an agent-written combinatorial expansion, not a proposition quoted from that page. Its proof is marked `proof_origin.by = agent`. The relevant published passage says that the arrow transformation determines S; the present split supplies the relative horn-filling details that the existing citer needs.

## What was wrong and what changed

I compared the returned sandbox against the current repository node and read all nine proof steps of its only citer, `lem-coef-infinity-arrow-join-geometry`. The returned sandbox had reused this id for a completed-pullback/Tor-amplitude claim. That is not a correction of this item. The repair restores the original statement, title, Kerodon source, statement dependencies, creation record, and genuine historical blueprint ancestry. In particular it again supplies P, Q, every P_H, the evaluation Q → X, the diagonal d, and the relative inner-anodyne inclusion, with no quasicategory assumption on X.

The proof now identifies a simplex of P with a pair (r,y), where y is a simplex of J and e(y) ≤ r. Under this explicit isomorphism Q is the union of the top row and the cylinder on the initial join fiber, and P_H consists exactly of the pairs with y in H. Unique nondegenerate decomposition reduces the missing cells to two chains A_(x,j), B_(x,j) for each mixed nondegenerate support x. Deleting t_j from B gives A; every other face is already present in the order (support dimension, then j). The missing face is inner. Filling these horns against an arbitrary inner fibration proves precisely the requested relative lifting property.

The inherited ancestry still passes through the stable-enhancement/arrow-join chain supporting paragraph 2 of `prop-coef-integral-exceptional-adjoint`. I also read the current main-20261015 proof of that ancestor. Its paragraph 1 uses completed pullback and the already existing `lemma-weil-pbc-completed-pullback-reduction`; it does not state the collage lemma. This discrepancy does not license changing this item's meaning. Any pruning or rerouting of the parent chain belongs to maintenance at the parent level. This delivery keeps the existing chain valid locally and makes no such rerouting.

## Repair of every finding in the return

1. **D1/E7/G2, identity reuse and broken citer:** restored the repository collage statement verbatim and discarded the unrelated replacement proof. Citer step 5 takes P,Q,evaluation,d; step 6 uses the explicitly constructed P_H and its support description; step 7 uses Q ∪ P_H → P inner anodyne. Each of these is again an actual clause of this node. All nine citer steps were read, and none was edited.
2. **C5/D1, redundant completed-pullback subclaim:** this delivery contains no such subclaim or new node. I read the statements of `lem-pur-integral-operations-preserve-constructible` (clause 1), `lem-sf-pullback-tor-amplitude`, and `lemma-weil-pbc-completed-pullback-reduction`, confirming that they belong to the different pullback argument. They are absent from the repaired proof and its dependency list.
3. **E1, missing global base-field hypotheses:** no application of the finite-field Tor-amplitude lemma remains. The repaired statement and proof are about arbitrary small simplicial sets. The only existence argument is inner-horn lifting for an arbitrary test inner fibration, which has exactly that lifting property by definition.
4. **B2/B5, incoherent statement/source/search metadata:** the restored statement now matches its title, source description, created.item, and all 13 retained simplicial searches. The false claim that five fresh pullback searches supported this collage split has been removed. The one added search was actually run with msearch: grep `pullback.*horn|horn.*pullback|triangular|collage`, subdirectory `AlgebraicTopology/SimplicialSet`; zero hits. The historical pullback log entries were retained without treating them as collage searches.
5. **No accepted tool uses:** the two previous pullback tool-use requests were removed. The only added proof dependency is an existing Mathlib leaf; there is no off-unit non-leaf theorem request.

## Review by Q25

I read the chapter and unit records, SETUP's three-level route rule, the stage-1 contract, and delivery-errors B–E. For the mathematical source I read Kerodon 0302 at the construction of S and its later prescribed slice-cone comparisons. I read the four cited DAG statements in full: `def-cbc-enhanced-diagrams-cones`, `def-coef-infinity-relative-join`, `lem-coef-inner-anodyne-pushout-product`, and `lem-weil-pbc-simplicial-set-nondegenerate-decomposition`. For the last node I additionally checked Stacks Tag 017R, `simplicial.tex`, `lemma-splitting-simplicial-sets`, and Mathlib `Degenerate.lean` at existence line 114 and uniqueness lines 217, 225, 233. No new node needs a separate source audit.

For step 1, the first two definitions really give the degreewise products, nerves, and join-block parameter used. I checked both maps of the normal-form identification: a chain gives its row and its pulled-back support, and the chain with one vertex of that row at every index gives the inverse. This is a direct calculation from the item's quotient, with no assumption that the individual support maps are embeddings.

For step 2, the relative-join definition supplies the pure initial factor and compatible target coordinate. The assertions about Q and P_H follow in both directions by the representatives in P_y; they are not taken from an unstated collage theorem. Here J_0 is explicitly defined as the entire initial simplicial fiber, not J's vertex set.

For step 3, the nondegenerate-decomposition leaf states existence and uniqueness of all three data, not merely existence of some degeneracy. That exact uniqueness proves the common-adjacent-repetition criterion for (r,y). A monotone surjection has a monotone section, so membership in H passes both to and from the nondegenerate support. These are the only facts about arbitrary degeneracies the later steps need.

For step 4, the chain classification is written out: once the last source index j is fixed, surjectivity forces every lower index into the source chain and every higher index into the target chain. Only t_j is optional. The cited nerve definition and decomposition statement suffice. Pure initial and pure final supports contribute no new cell; no n = 0 mixed support exists.

For step 5, I checked every codimension-one face, including deletion of s_j, deletion of t_j, and all faces omitting an index. The cited definition says a horn is the union of every face except the specified one. The missing vertex has position j+1, with 0 < j+1 < n+1 because j ≤ i < n. This verifies the inner-horn hypothesis, rather than using an outer horn accidentally.

For step 6, the same decomposition leaf really gives the uniqueness used to prevent identifications of new interiors, even when boundary faces of a simplex coincide. Boundary identifications are allowed and already respected. Supports outside H cannot appear in P_H because they are recovered by a simplicial section. This is why the proof works for arbitrary H, not just the empty subset.

For step 7, the cited inner-anodyne node explicitly defines inner fibrations by their right lifting property and inner anodyne maps by the left lifting property. I use these definitions directly: construct the lift in the specified well-founded order, with all choices taken over small sets. The earlier face and uniqueness arguments prove compatibility. There is no unquoted theorem asserting that an arbitrary pullback of an inner-anodyne map is inner anodyne, and no unquoted model-category closure or cellular-attachment theorem.

For step 8, the functor definition supplies the evaluation formula, and the relative-join definition supplies p_X and the endpoint agreement. Evaluation on the cylinder and p_X on the top row coincide exactly on their intersection, including degenerate simplices. For step 9, the diagonal is the explicit pair (e(y),y); precomposition proves it simplicial and gives the required pure-factor chains. These steps construct the two actual maps needed by citer steps 5–7.

All non-elementary outside input is therefore a cited statement; the other assertions are the displayed quotient inverses, chain enumeration, face calculation, and formulas for this item's objects. No source's hidden standard lemma has been moved into a new clause-equivalent node. The whole-DAG keyword search and whole-blueprint searches for `inner anodyne`, `prism`, and `nondegenerate` were read. The existing decomposition leaf was reused; the triangular-top-deletion and twisted-pullback-boundary nodes concern different posets and are not silently substituted here.

The Mathlib searches inherited from the sandbox include two distinct natural-language formulations and valid Loogle, LeanFinder, LeanSearch, and source-grep results. I read their recorded hits and the candidate source interfaces in `Inner/Basic.lean` and `Inner/PushoutProduct.lean`. Those provide horn/pairing and pushout-product infrastructure, not this relative collage inclusion as an exact result or a one-line specialization. The nondegenerate-decomposition candidate was already represented by a Mathlib leaf and was reused. No unrun query was added and no service failure was treated as evidence of absence.

For small cases I checked X empty, B empty, H empty, H = J, pure initial and final supports, and mixed supports (n,i) = (1,0), (2,0), (2,1). The first mixed case is the ordinary inner 2-horn. A sandbox Python enumeration checked every strict chain for all 35 posets with n = 0 through 6 and i = -1 through n: all 56 claimed attachments have precisely the specified inner horn as intersection, add exactly A and B, and exhaust the missing chains. The script is finite combinatorics, not a Lean compiler. For nonembedded or degenerate support maps, step 3's uniqueness and step 6's boundary argument supply the general justification; the enumeration is only a check on the local face formula.

Each of the nine proof steps is below 2000 characters (maximum 1066). The proof does not acquire a field, finite-type, fullness, or quasicategory hypothesis. The statement is byte-for-byte the repository statement. All 17 quotations were checked as literal substrings of the cited statements. No statement dispute remains.

## Not duplicates

No new nodes. The decomposition fact is cited by its existing id, not recreated. The discarded completed-pullback statement is not delivered under any id.

## Unfinished work

No unfinished mathematical part of this item. The missing Kerodon archival copy and possible parent-level ancestry pruning are reported above; neither is used to replace or weaken the collage statement. Only stage 1 was performed. Server `review_split` passed before this report was finalized; the full required dry run and delivery follow.
