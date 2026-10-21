# Worker report: lem-sf-constructible-canonical-completeness

## Files written

- `dag/nodes/sec-six-functors/lem-sf-constructible-canonical-completeness.json`: statement item, split into six steps; Mathlib verdict no match. The statement and its six statement dependencies are unchanged. No new nodes, no Mathlib leaves.
- `citations.json`: twelve citation occurrences, each with an excerpt verified literally against the cited node's statement.
- `report.md`: this report. `searches.jsonl` is the search command's original log; `write_split.py` is sandbox-only preparation code, not a delivery file.

## Attachments

None. Searched `lean/WeilConjectures/` for the blueprint id and for constructible/canonical completion and intrinsic/Koszul completeness terminology. No declaration there states all clauses. The relevant actual witness argument is instead in `lean/Sheaf/Paper/WeilTensorProduct.lean`, private `wfComplete_of_presentation` (line 976) and public `wfConstructible_complete` (line 1548). These are reference material for this split, not an authorized upstream attachment.

## WANTED

None. The item is a source-interface refinement written by an agent; it is not attributed as a verbatim theorem of Stacks.

## Findings and changes

The imported item had no proof. Its source mentions the base proof's Step 10, while the live parent `def-wf-tensor-product` now places `wfConstructible_complete` in Step 4. Both references mean the same witness/round-trip/canonical-completion obligation. I retained the imported source information and named the obligation in `split_report.blueprint`.

The current natural-language `def-weil-pbc-bounded-constructible-complete` states intrinsic completeness directly, whereas its Lean interface and this item's hypothesis expose an existential presentation witness. I did not silently treat the definition node as an existence theorem for the literal tuple. Step 6 explicitly distinguishes its two presentations: the witness encoding uses Steps 1--5, and a directly stated actual witness starts at Step 3. No hypothesis or conclusion of this item was changed.

The existing generic `lem-cbc-exact-linear-koszul-fiber` already states the signed fiber and prescribed-unit transport. The existing `lem-weil-pbc-completed-constant-presentation-transport` already supplies both normalized comparisons to a common quotient completion. Creating further nodes for either fact, for the independence clause of this item, or for cancellation of isomorphisms would duplicate statements or merely relabel this item. I reuse those nodes and keep the cancellations in the proof.

Mathlib searches were run using the mandatory msearch command and recorded directly from its log. Loogle and grep had no hits. The first LeanFinder query returned invertible-module and algebraic extension facts. LeanSearch returned site-equivalence unit formulas. The second semantic phrasing returned ordinary adic module completion, local cohomology, and finite-presentation sheaves. None states derived sheaf completion with these specified units and arbitrary finite generator lists. The old item search records are retained unchanged; five actual Q36 searches are appended.

## Not duplicates

No new node is created, so there are no new/existing pairs to distinguish. Whole-blueprint searches for completion and Koszul were read. The existing intrinsic-to-tower-complete node gives only the quotient-unit conclusion and does not remove the need to prove this item's arbitrary actual-unit conclusion. The actual Koszul/quotient comparison has no completeness assumption and is a comparison tool, whereas this item derives invertibility from a presentation witness.

## Tool uses

The five statement tools named in `split_report.tool_uses` serve coefficient equivalences, exact products, exact functor passage to derived categories, the explicit signed-fiber comparison, and the two normalized presentation comparisons. They are generic tools under the ambient tensor convention. The unit `sk-rem-sf-pf-done` is a remark discharging projection-formula obligations and contains no alternative coefficient-presentation argument. This split neither replaces a unit-level projection-formula route nor invokes duality or any SGA source.

## Review by Q36

I read the item's chapter and unit records, the current parent tensor-convention node and the main-20261015 tensor blueprint text. That text only gives the tensor convention; it does not prove this coefficient-category refinement. I read Stacks algebraization.tex Tag 0A0E, label `lemma-derived-completion-koszul` (lines 1091 onward), and proetale.tex Tag 099M, label `lemma-naive-completion` (lines 4305 onward). The former gives the finite Koszul tower over a general ringed site and the latter the Noetherian quotient-tower formula. The extra exact-equivalence and canonical-unit comparisons are explicitly agent-written and supplied by existing cited nodes. There are no new-node sources to certify.

For Step 1 I opened the coefficient-equivalence statement: it really gives an additive equivalence naturally isomorphic to fixed small-site transport and inverse scalar restriction, with a scalar-preserving coefficient isomorphism. This gives A-linearity on morphisms. The proof explains A-linearity of its inverse through counit conjugation, and explains product preservation using the Hom universal property. I opened det-pe-products-exact: its statement applies to any ring sheaf on the pro-etale site, hence to the actual completed ring. Transporting short exact sequences through the given exact equivalence supplies exact products in the presentation category. I opened the exact-derived-functor statement: it says precisely that the exact module functors act termwise on complexes and derived categories, so their unit and counit induce the derived equivalence used here.

For Step 2 I read the whole exact-linear Koszul-fiber statement. It assumes additive exact A-linearity, invertibility of the projection-characterized countable-product comparison, and exact products on both sides. Step 1 verifies all of them. It concludes a chain isomorphism preserving the literal signed differential and the unit (u,0), not merely some map of triangles. I also read def-weil-pbc-intrinsic-completion: its transition maps are multiplication by the scalar in degree -1 and identity in degree 0; its fiber differential is (dx,(1-s)x-dy), matching the transport lemma. This identifies the witness unit on D_0=G(C). The derived exact-functor statement justifies QG(C) versus D(G)Q(C); applying D(G) to j and using the inverse unit gives e_0 with the correct direction. No strict representative for j is required.

For Steps 3 and 4 I opened the completed-constant-presentation-transport statement. It asserts existence of an equivalence and, for every generating list and every actual complex, a comparison carrying its specified Koszul unit to the same constant quotient-completion unit. Its hypotheses are exactly the adic datum already in force; it imposes no boundedness, constructibility or completeness hypothesis. I used an auxiliary H rather than identifying its chosen equivalence with the hypothesis's F. Naturality at H(e_0) gives invertibility of the constant unit at H(M). For arbitrary a,D,i the equation is H(eta);c_D;L(H(i))=mu, with the inverse of i on the source. This checks the normalization and all directions explicitly. Every remaining inference is composition or cancellation of isomorphisms; the reflection argument is applying the inverse equivalence and its unit. Thus independence of generating tuples is deduced through a common quotient completion, not asserted from a definition or from a cofinality argument left unstated.

For Step 5 I separately checked the presentation-transport statement's first clause: it compares the actual strict quotient derived limit and its constant/limit-adjunction-plus-augmentation unit to the constant completion unit. The citation excerpt for this step is that clause, not the Koszul clause. I read def-weil-pbc-completed-pullback to check that this is the canonical strict tower unit claimed by the item. Its identity-morphism specialization is the stated unit; this step does not replace it with an arbitrary cone map. The stipulated tuple and representative are specializations of Step 4.

For Step 6 I read the bounded constructible complete definition in full. Intrinsic completeness is its first condition, and neither its uniform constructibility nor its compatible etale-origin conditions are used. Its specialization to a valuation ring and noetherian finite-dimensional schemes is within the already proved general result, not an added hypothesis on the general statement. As noted above, the literal existential presentation encoding comes from the item's explicit hypothesis/Lean interface, not a spurious quote from the definition node.

I tested the statement on M=0 (all units are between zero objects), the zero coefficient ring (only the zero module), I=0 with an empty generator list (the Koszul tower is constant with identity transitions and its derived limit is the original object), repeated/zero added generators (the quotient target is unchanged), and I=A (the completed ring is zero). No regular-sequence hypothesis is needed for the bounded finite-free Koszul complexes. All tuples are finite, all products are countable, and all sites use the chosen small presentation with the specified coefficient universe. No step exceeds 2000 characters; none hides an additional comparison theorem. I checked B1--B10, C1--C8, D1--D5 and E1--E7 against these statements: no new unsplit proof-bearing node, false attachment, uncited non-elementary comparison, unsupported strengthening, cyclic use of the item, source-route replacement, or SGA citation was introduced.

## Unfinished work

No mathematical part of the one-level split remains. The required server dry run exited 0 and printed `OK (not pushed)` at dry-run commit `6e62cb4c39c`; preflight passed. Direct delivery is performed by the required deliver.py command, which rechecks the final report and files before pushing.
