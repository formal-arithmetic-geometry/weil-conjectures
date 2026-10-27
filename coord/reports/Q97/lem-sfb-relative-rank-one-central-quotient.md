# Q97 stage-1 delivery

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-rank-one-central-quotient.json: item, statement unchanged, complete five-step split.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-reductive-centre-weight-kernel.json: statement-only general relative centre theorem, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-relative-central-multiplicative-quotient.json: statement-only general relative central-quotient theorem, unsplit; no Mathlib match.
- citations.json: verbatim statement excerpts for every proof-step citation.
- searches.jsonl: unedited actual search-command records; existing searches in the item's imported record retained.

Two new nodes, zero Mathlib leaves. No Lean files written and no compiler, Lake or build tool invoked. The read clone and launcher were not modified.

## Attachments

None. Searched the item tag and rank-one/central-quotient notions in lean/WeilConjectures, including GroupScheme and LinearAlgebraicGroup. The matrix-group centre theorem in GroupScheme/GeneralLinear/ClosedSubgroup.lean, lines 702--710, concerns a reduced centre over an algebraically closed field, not the relative scheme-theoretic centre, and does not attach this item or either general input.

## Literature wanted

WANTED: Brian Conrad, Reductive group schemes, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, Theorem 3.3.4, Corollaries 3.3.5--3.3.6, Appendix B.1 and the opening proof of Theorem 5.1.8, for this item and the two new nodes; local name literature/conrad-reductive-group-schemes.pdf. The PDF is absent locally; I read the primary document online. No SGA document was used as a source. There is no Stacks tag for these relative reductive structural assertions; the source records give Conrad's named places rather than inventing a tag.

## Audit of the imported item and route

The imported statement is retained, including arbitrary base change, the torsor identity, maximal-torus inverse image, and the scheme-theoretic finite centre. No statement dispute was found. The zero ring is excluded as in the item. The item had no proof and no Lean attachment. Its source's local WANTED notice remains accurate.

I read AGENTS.md, GOAL.md, the human's three blueprint levels in SETUP.md, the worker and stage-1 documents and delivery-errors.md B--E (including the merged copy). I read the chapter and unit records and the current latest blueprint (ef6f9619), particularly sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. This split stays below the inherited supporting structural branch; it does not replace any unit step. The very long inherited ancestor place remains unchanged. blueprint_refs.py ancestor gives None, agreeing with the existing from.node=null; the new nodes inherit that result and prepend this item to via. Searches of the whole imported blueprint for reductive, torus, diagonalizable, central quotient and multiplicative type found no matching blueprint statement. The broad adjoint search produced unrelated categorical adjunctions, not a group-scheme centre statement. same_as remains empty.

## Not duplicates

lem-sfb-relative-reductive-centre-weight-kernel vs lem-sfb-reductive-centre-multiplicative-type: the existing node is over fields and asserts multiplicative type only; the new node proves representability over a ring, arbitrary-base-change compatibility, and the torus-action kernel and constant-weight character formula.
lem-sfb-relative-reductive-centre-weight-kernel vs lem-sfb-reductive-borel-pair-structure: the existing node gives the field root datum and Borel structure; it does not identify the relative schematic centre.
lem-sfb-relative-reductive-centre-weight-kernel vs lem-sfb-relative-rank-one-central-quotient: the new node is the general centre/action-kernel input in any rank, including empty roots, not the rank-one reduction, primitive torus, rank bound or construction of H.
lem-sfb-relative-central-multiplicative-quotient vs lem-sfb-affine-normal-quotient-geometry: the existing theorem is over a field and does not state reductivity, the centre quotient or the maximal-torus correspondence. The new node works over rings and includes arbitrary base change.
lem-sfb-relative-central-multiplicative-quotient vs lem-sfb-reductive-central-pushout-reconstruction: that field theorem reconstructs a group from a universal multiplicative covering; it does not give the relative quotient theorem used here.
lem-sfb-relative-central-multiplicative-quotient vs lem-sfb-relative-rank-one-central-quotient: the new theorem is the general central multiplicative-type quotient tool for every reductive rank and every such central subgroup. It neither selects the saturated root kernel nor computes the finite centre in rank one. The item performs both computations explicitly.
lem-sfb-relative-central-multiplicative-quotient vs lem-sfb-relative-rank-one-semisimple-models: that node classifies a quotient once it already exists and has centre of order 1 or 2; the new node supplies the general relative quotient and torus theorem without classifying any rank-one model.

Global DAG statement searches (rather than only the current chapter), the existing source-place matches, blueprint_refs.py searches, and Lean searches preceded creation. Existing field classification, radical and diagonalizable duality nodes are reused. No new elementary lattice, monic-polynomial or trivial-torus-to-finite-group node was created. Neither new node is a restatement of one rank-one clause: both are standard general structural inputs whose rank-one consequences are calculated in the item.

## Review by Q97

I read Conrad's Theorem 3.3.4 and its weight-space construction on printed pp.98--100, Corollaries 3.3.5 and 3.3.6 on pp.100--101, Example 5.1.7 on p.138 and the first paragraph of the proof of Theorem 5.1.8 on p.139. For the new centre node these give the actual functorial schematic centre and its character kernel, not just its geometric points. The constant-support hypothesis in the new statement is explicit: it avoids using a single global list of weights where the roots could vary between components. It does not assume globally trivial root lines. For the new quotient node I also read the quotient discussion in Lemmas 3.3.1--3.3.2 on pp.96--98: it supplies the represented affine quotient; Corollary 3.3.5 supplies reductivity, the centre and torus correspondence. The torsor identity follows from the represented fppf quotient: locally two representatives differ uniquely by C, and the local representatives glue. Thus the quotient assertions are about sheaves and schemes, not a false assertion that G(R) surjects onto Q(R) for every R.

Step 1 uses precisely the statement of lem-sfb-split-rank-one-classification, opened and read: its hypotheses are algebraically closed field, reductive group, maximal torus, and semisimple rank one. Every geometric fibre here meets them. The listed pairs explicitly include their diagonal tori. Diagonal conjugation gives characters 2e, e, e1-e2; central factors contribute zero. These calculations yield all nonzero fibre roots and the integral divisibility 1 or 2, also in characteristic two. No relative matrix classification is assumed. This avoids any circular use of the item's parent or the new semisimple-model node.

Step 2 uses the new centre node's exact constant-weight formula. Step 1 verifies its support hypothesis at every geometric point, and the original split maximal torus supplies M. In particular this step does not use the generally invalid principle that equality on geometric fibres proves equality of arbitrary closed subschemes.

Step 3 uses lem-sfb-relative-diagonalizable-character-duality, whose full statement I read: it covers kernels and fppf quotients over a nonzero ring, including torsion character groups and nonreduced rings. Euclidean row operations send the primitive vector to e1; the two equations z1=1 and z1^d=1 show the central inclusion directly. This is an elementary lattice calculation plus the cited character theorem, not an unrecorded relative structural theorem.

Step 4 uses the new central multiplicative quotient theorem only after Step 3 has exhibited K as a split, hence multiplicative-type, central torus. Its statement explicitly gives the reductive quotient, faithful flatness, finite presentation, torsor identity, centre and maximal torus with inverse image. Character duality applies again to the finitely generated group N=M/Z alpha and subgroup L=Z alpha0/Z alpha, with N/L=M/Z alpha0. Consequently the quotient of centres is D(L), not a quotient with the lattice arrows reversed. The map k mod d to k alpha0 identifies L with Z/dZ. The explicit monic coordinate algebra has the stated free basis, including d=1.

Step 5 uses lem-sfb-reductive-radical-quotient, opened and read, on the geometric fibres of the now constructed reductive H. It states that the radical is the largest subtorus of the centre. A map from a torus to mu_d is zero because the corresponding homomorphism from the finite character group Z/dZ to a free lattice is zero. Hence the radical is trivial and the maximal torus of dimension one measures semisimple rank one. Character duality's homomorphism classification supplies this argument even when mu_2 is not reduced. The two new relative structural nodes and the existing duality node explicitly supply arbitrary-base-change compatibility; writing the same equations and monic basis after A to B confirms the remaining elementary assertions. citations.json includes a verbatim portion of every cited statement, checked as literal substrings. proof_deps equals exactly the union of uses.

For small cases I checked SL2 (d=2), PGL2 (d=1), GL2 (primitive e1-e2, scalar K and trivial quotient centre), and their products with a split central torus; r=1 gives K=1. Over characteristic two the SL2 centre remains the finite flat nonreduced mu_2, so no smoothness, etaleness or reducedness of the centre is asserted. The same equations work over dual-number bases. Over disconnected bases the fixed alpha makes its divisibility independent of the component, as required. For the general centre input the torus case has empty Phi and recovers Z(G)=G. For the general quotient input C=1 and SL2/mu_2=PGL2 check the extreme cases and the nonsmooth-kernel case.

During review I corrected the new centre source pinpoint from Proposition 5.1.6 to Example 5.1.7, and allocated the recorded searches to the statements they actually address. The retained search records and results are the actual command output summaries, with no invented searches. Each new node has natural-language semantic searches in two phrasings, Loogle and Mathlib grep; the hits concern Lie-algebra kernels, abstract centres or adjunctions and do not specialize to these relative theorems. New nodes have statements only, no proof or hidden proof in their statements. All five item steps are below 700 characters, so no long step hides an additional lemma. A dependency traversal confirms none of the reused inputs reaches the item. No hypotheses were added or conclusion weakened. Nothing mathematical remains unfinished in this one-level split; the two general structural inputs are deliberately statement-only future items.

## Validation

The remote review_split check passed before the report. Final delivery dry run and push are recorded by the delivery command after this report is written.
