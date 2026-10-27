## Worker report

Item: lem-sfb-dg-compact-bimodule-full-faithfulness. Group NJ. Stage 1 only, direct delivery, 2026-10-24.

### Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-compact-bimodule-full-faithfulness.json: split, five proof steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-semifree-bimodule-tensor-computation.json: statement, unsplit; no Mathlib match. Computes derived bimodule tensor on all semi-free source modules as an isomorphism in D(B,d), including its action on module maps.
- citations.json: ten verbatim statement quotations, one for each step/cited-node pair.

One new node, zero Mathlib leaves. No Lean written or compiled; no repository or launcher file edited, and no git command run by the worker. The sandbox had no earlier node or report to retain.

### Attachments

None. Searches of lean/WeilConjectures/ for the item id and DG algebra/module and bimodule vocabulary found ordinary module-object bimodule constructions, not this derived DG full-faithfulness criterion. The proposed computation node also has no existing project declaration. No sorry-containing declaration was treated as a finished proof.

### WANTED

None. The proof and new computational input follow the available literature/stacks-project/dga.tex.

### Findings and corrections

The item itself is correct and keeps its exact statement. Stacks Tag 09R9 (lemma-tensor-with-compact-fully-faithful) has two adjoint-direction typos in its prose: its proof calls RHom a left adjoint, whereas Tag 09LT (lemma-tensor-hom-adjoint) explicitly gives tensor as the LEFT adjoint to RHom; the preceding example-map-hom-tensor has the same prose reversal. The displayed unit M -> RHom(N,T(M)) and the proof are consistent with the correct adjunction. Our proof uses the exact adjunction in the existing node, without reproducing those typos. There is no change to the item's statement or to the unit/chapter route.

The existing lem-sfb-dg-adjunction-compact-unit supplies precisely the property-(P)/compactness extension in the source proof, so no new generator, coproduct-of-Hom, or full-faithfulness criterion was introduced. The present work still verifies its substantive missing hypothesis: the actual specified unit at A is invertible. It does so by computing the action of tensor on a cycle map A -> A[k], then using the adjunction transpose, not merely by observing an abstract isomorphism of two groups.

The only new node is the non-elementary computation theorem behind the evaluation of a left derived functor on semi-free DG modules. Its conclusion is in D(B,d), with the B-action and naturality for DG maps. The unitor, its shifts, and the multiplication-map computation are proved in step 2 rather than made into nodes. Step 4 uses a genuine DG representative of the unit supplied by shifted-free Hom, so that cohomology detection follows directly from the definition of localization; no uncited general roof-calculus or generator theorem is used.

### Searches and blueprint

Read AGENTS.md, GOAL.md, the stage-1 worker brief, stages/1-dag.md, roles/worker.md, SETUP.md's three levels, and delivery-errors B through E. Read the chapter/unit JSON records, together with the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Its paragraph (3) is the recorded ancestor route. The older imported unit JSON and latest unit prose differ; no unit claim or route is changed here. tools/blueprint_refs.py ancestor prints None for this item's existing created-item chain; the new node retains that computed ancestor and adds this item to the inherited via chain.

DAG searches covered the item tag 09R9, tag 09LS, lemma-derived-bc, remark-shift-tensor-no-sign, compact/unit/adjunction, and semi-free/property-(P) tensor statements across all dag/nodes. Existing free Hom, compact-unit, DG triangles and coproduct nodes are reused. Whole-blueprint searches were run for compact, DG bimodule, dg coproduct, tensor.*free, compact.*fully faithful, semi-free tensor, semi-free, and derived tensor; the broad tensor hits are sheaf/commutative-ring tensor constructions rather than this DG bimodule computation. The same_as lists are empty.

All new Mathlib-search records come from the actual msearch.py output logged in searches.jsonl. LeanFinder, LeanSearch, Loogle and grep all ran, with a second semantic phrasing for both the item and the new statement. The hits were ordinary HomologicalComplex tensor constructors, classical Tor and full/faithful single functors. I read the relevant pinned Mathlib sources: Algebra/Homology/Monoidal.lean (HasTensor, tensorObj and the tensor inclusion, lines 41-57), CategoryTheory/Monoidal/Tor.lean (Tor, Tor' and projective vanishing), and Algebra/Homology/DerivedCategory/FullyFaithful.lean (singleFunctor full/faithful). They neither provide a DG A-module resolution computation valued in D(B,d) nor the item's compact-bimodule criterion. No Mathlib leaf is claimed.

### Unfinished work

No part of the item's split remains unfinished. The new computation theorem is deliberately statement-only and unsplit, as required for a one-level stage-1 split. The existing compact-unit propagation theorem remains its own item and is cited for exactly its stated conclusion.

## Not duplicates

lem-sfb-dg-semifree-bimodule-tensor-computation vs lem-coef-dg-two-sided-bar-derived-tensor: the latter states derived balanced tensor of a right and a left DG-category module as an integral complex, with an additional flat bar-model clause. It does not state a comparison in the derived category of right DG B-modules retaining an independent target algebra action. The new node states that D(B,d)-valued comparison for a general (A,B)-bimodule, natural on semi-free source maps, without the bar-model or base-flatness assumptions. It is this target-action comparison, not a new copy of the integral bar calculation, that step 2 needs.

lem-sfb-dg-semifree-bimodule-tensor-computation vs lem-sfb-dg-bimodule-derived-adjunction: the latter supplies existence, exactness, a K-injective model for Hom and the tensor-Hom adjunction, but does not state which source modules compute the left derived tensor without replacement. The new statement supplies that computation on every property-(P) module.

lem-sfb-dg-semifree-bimodule-tensor-computation vs lem-sfb-dg-compact-bimodule-full-faithfulness: the new statement assumes no compactness or self-extension isomorphisms and concludes no full faithfulness. It is a computational input, not the item or one of its conclusion clauses.

## Review by NJ

I read Tag 09R9's statement and proof in dga.tex and checked the surrounding Tag 09LT adjunction, Tag 09LS derived-bc proof, section-P-resolutions, and Tag 0FQN shift-tensor formula. Tag 09R9 says exactly the item's two hypotheses and full-faithfulness conclusion, and does not require N to generate the target. I corrected only the adjoint-direction typo in the proof narrative as described above. For the new node, Tag 09LS explicitly constructs the derived functor using modules with property (P); its proof computes on that collection in D(B,d). section-P-resolutions gives the precise exhaustive graded-split filtration and direct sums of shifts. These match every hypothesis of the new statement; its naturality is the comparison of functors on that computation subcategory, hence concerns f tensor id with the original right B-action. I did not use the theorem about tensoring with a left semi-free bimodule in place of this right-source computation.

For step 1, I opened lem-sfb-dg-bimodule-derived-adjunction: its statement specifies T dashv U, their exactness, and shift compatibility of the actual unit. I opened lem-sfb-dg-derived-admissible-triangles: it states that the DG derived category is triangulated. I opened lem-sfb-dg-sequential-colimit-triangle: its statement explicitly includes all small coproducts represented by DG direct sums, independently of its telescope clause. Finally, lem-weil-pbc-left-adjoint-preserves-colimits states exactly preservation of the specified colimit cocones by a left adjoint; apply it to small discrete index categories. These verify all categorical hypotheses, with the same universes and no countability restriction. Only the last citation is off-unit, and it is already a Mathlib leaf; no new route/tool approval is needed.

For step 2, I checked the new computational statement itself: it gives the D(B,d) comparison and its naturality for the module map f_a. A[k] has property (P) with one nonzero quotient. The remaining formulas are elementary balancing and differential calculations: for shifted degree i the tensor differential has signs (-1)^k on d_A and (-1)^i on d_N; multiplication matches (-1)^k d_N on N[k]. The inverse 1 tensor n and the formula (f_a tensor id)(1 tensor n)=a tensor n show the actual action map without an unproved identification. This step uses none of the item's compactness or self-Ext assumptions.

For step 3, lem-sfb-dg-free-module-hom-cohomology states the canonical cycle-to-morphism isomorphism, with the correct unchanged right action on shifts. The adjunction node states the actual chain currying and shift compatibility, not just existence of an arbitrary adjunction. The equation eta_{A[k]} f=UT(f) eta_A follows from naturality, and is the transpose of T(f) by the adjunction formula. The item's assumption therefore makes precisely Hom(A,eta_A[k]) bijective. This is a short categorical calculation from the cited statements, marked elementary, not a new full-faithfulness criterion.

For step 4, lem-sfb-dg-free-shift-derived-hom states that EVERY derived map from A[k] is represented by a genuine DG map, without flatness or boundedness. Applied at k=0, it supplies u:A -> C representing the unit. The cohomology formula then makes H^k(u) bijective for all positive, negative and zero k. Inverting this quasi-isomorphism is the defining operation of D(A,d). This avoids silently using the abelian-category derived-category iso test for DG modules.

For step 5, I read the entire statement of lem-sfb-dg-adjunction-compact-unit. Its domain is the same unbounded DG derived category; its target is any triangulated category with all small coproducts; its assumptions are exactness, a specified shift-compatible adjunction, T preserving small coproducts, compactness of T(A), and invertibility of eta_A. Steps 1-4 and the compactness hypothesis verify these individually. Its statement explicitly gives invertibility for all units and full faithfulness without a target-generation hypothesis. We do not use any argument hidden in its proof, and it has no dependency on this item.

I tested the computational statement at P=0, arbitrary A[k], an infinite direct sum of free shifts, and B or N zero: the comparison is valid with the same right action and no finite-rank/flatness hypothesis. For the item, N=0 forces H^*(A)=0 by the self-extension assumption, so the conclusion only asserts full faithfulness from the zero derived category. The identity bimodule N=A gives the identity tensor. Taking A=Z and N=(Z,0) in D(Z) x D(Z) shows why target generation must not be added. Nonconnective A and negative shifts are covered, and no commutativity or countability is used. The new node is self-contained, its DG notions and filtration are written out, its derived functor cites its exact defining node, and it has no proof/proof-dependency fields filled. No new statement is a clause of the item. Every cited statement was read, every quotation is a verbatim substring, and every non-elementary step has its required nodes. All five steps are shorter than 2000 characters; the only new substantive theorem is separated into its own statement-only node. No SGA source is used.
