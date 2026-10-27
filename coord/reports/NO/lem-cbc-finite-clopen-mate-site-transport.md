## Worker report

Files written: `dag/nodes/sec-smooth-purity/lem-cbc-finite-clopen-mate-site-transport.json` (statement, now split in seven steps; no Mathlib match), this report, and `citations.json` (25 verbatim statement witnesses). The sandbox initially contained no item, proof, report or search history. The inherited item statement, provenance and searches are retained; five actually executed Mathlib searches are appended from `searches.jsonl`.

Attachments: none. I searched `lean/WeilConjectures/` for the blueprint tag, clopen mates, finite-clopen and proper/open terminology. Its clopen trace and cohomology results do not state the item. The upstream declarations with sorry are not evidence of completion. No Lean was written or compiled.

WANTED: none. The extra counit calculation is an agent-written argument using archived Stacks material and existing DAG statements, rather than a claim that Stacks 09AF states the complete result.

The item has no statement error requiring correction. Its empty proof needed an explicit verification of the *named* transport morphism. An abstract existence of an isomorphism between the endpoint objects would not suffice. I added the direct-image, inverse-image, both open-extension and quasi-separated definition dependencies needed to read its notation. I did not change any other node.

Unfinished work: none at this splitting level. Existing unsplit dependencies remain their own items.

## New nodes

None; 0 new nodes and 0 Mathlib leaves. In particular I did not introduce a node for either one of the item's own transport clauses. The clopen geometry and etale K-injective mate normalization already have the exact specialized statement `lem-cbc-etale-clopen-mate-normalization`; the direct-image comparison already has the exact normalized statement `lem-weil-pbc-comparison-direct-image-canonical-mate`.

## Searches and route

I read SETUP's three levels, GOAL, the stage-1 brief and worker role, the stage document, the unit `sk-prop-sf-cbc` and chapter `sec-smooth-purity`, and both copies of delivery-errors sections B–E. This is the finite-normalization input to the compactification-compatibility parenthesis in the last sentence of the current `thm-cbc-complete-proetale.proof.md` (main-20261015, sec-six-functors-basics/sk-thm-sf-pf-adic), via `lem-cbc-strict-tower-proper-open-calculus` steps 14–15. I did not use that parent theorem as a dependency.

Whole-DAG searches by clopen, mate/comparison, 099R, 09AF, and the exact normalization names found the existing inputs. `blueprint_refs.py ancestor` reports thm-cbc-complete-proetale; whole-blueprint searches for "clopen mate", "clopen projection" and "counit-normalized" return no duplicate. The five "proper/open" hits concern compact-support assembly, refinement-specific comparisons or restricted ambient finite-type settings, not this square and its specified counit transport.

Mathlib searches were made only with the prescribed msearch command. The first semantic phrasing found condensed/topological adjunctions; the second found `CategoryTheory.mateEquiv_counit`, `mateEquiv_square` and related generic calculus. Loogle's conjunction returned zero hits. Grep found mate pasting declarations at Mathlib/CategoryTheory/Adjunction/Mates.lean:170,209, which I read: they have arbitrary categories and no sites, clopen supports or proper/open normalization. LeanSearch found open-map adjunctions, scheme-module restriction and algebraic etale declarations. None states the item or specializes to the entire item in one line. All services answered successfully and the exact queries/results are recorded. The generic mate calculus is not a new node: the existing mate definition already supplies its explicit transpose bijection.

Off-unit inputs are declared in split_report.tool_uses: separated implies quasi-separated, exact etale extension, and the two geometric site comparisons. These are generic tools, used with exactly their hypotheses, rather than a replacement of the unit's compact-support route. Definition nodes only provide the named conventions and formula for a mate.

## Not duplicates

No new-node/existing-node pairs: no new nodes are created.

## Review by NO

I read Stacks proetale.tex Tag 099R, section-comparison, including its inverse-image description, and Tag 09AF, lemma-jshriek-comparison: its proof identifies the two left adjoints. I read more-etale.tex Tag 0F7B, lemma-shriek-proper-and-open, especially the explicit K-injective arrow in the first paragraph. This is the resolution normalization in the item, not merely an unnamed isomorphism. I also read categories.tex Tag 0B65, lemma-transformation-between-functors-and-adjoints, with its counit diagram and uniqueness proof; sites-modules.tex Tag 03DJ, lemma-extension-by-zero-exact; and schemes.tex Tag 01K7, lemma-closed-immersion-quasi-compact. There are no new-node sources to audit and no SGA source is used.

For step 1 I opened the proper and finite-type definitions, the separated/quasi-separated lemma, exact etale extension, and canonical direct-image mate statement. Proper means separated and finite type, supplying qcqs without any Noetherian condition. Exact extension commutes with kernels/images and hence cohomology, so k_!L has L's lower bound. The canonical comparison states invertibility for the named b, at precisely qcqs u and D+ input: I checked both substitutions (r,L) and (p,k_!L). A finite ring is given its discrete topology.

For step 2 I opened both extension-zero base-change statements, the pullback comparison, open site comparison and mate definition. The first two give the beta isomorphisms in the actual etale/pro-etale coefficient categories. Pullback comparison explicitly includes cartesian and compositor compatibility, and the open comparison is the adjoint one specified in the item. Transposing the inverse beta reduces its compatibility to the open unit, which is preserved by that adjoint comparison. The step writes this transpose, rather than citing a general fully-faithful result as a Yoneda theorem or presuming arbitrary isomorphisms preserve units.

For step 3 I checked the statement of the etale clopen normalization node: it explicitly forms the same W_S, s and clopen projection, with no cartesian or identity-left condition. I use its geometry, not the tower-only projector assertion of a sibling node. The small argument is ordinary sheaf gluing over two disjoint opens: matching pairs have unique glued sections and the overlap is empty. The pullback/open comparisons preserve their restrictions and the zero and identity arrows. This proves the projection identity as a sheaf-map identity before applying complexes or localization; it does not assume derived restriction is faithful. Its elementary designation refers to this written binary-gluing argument.

For step 4 I checked that the open comparison states compatibility with open composition and that pullback comparison states compatibility with composites and the cartesian identification. Their use with bs=k and qs=r gives the displayed alpha equation; both its source and target are written in the step. The etale normalization node explicitly identifies the *derived mate* with the K-injective-resolution arrow and explicitly includes the refinement case. No property is taken only from its proof.

For step 5 I opened the mate definition again: its transpose is exactly H epsilon composed with alpha R. Naturality in b_r moves b_r across alpha, and the actual canonical-mate statement supplies epsilon_r^p G_r^p(b_r) a_r = A(epsilon_r^e). This leaves the exact expression shown, using naturality of o_k. All functors have matching domains: X is on T_proet and Y is on W_proet.

For step 6 the same definition and the p counit equation at J_k^eL yield the other transpose. Naturality of a_p is used at gamma^e, whose target is R_p^eJ_k^eL, so the comparison index is checked rather than suppressed. The etale mate equation makes the parenthesis identical to step 5. Cancelling a_p and applying the adjunction bijection proves the required equality. This is an explicit formal calculation with the cited statements, not an additional hidden site-comparison lemma.

For step 7 I read the full statement of proper/open interchange: it supplies invertibility for a commutative square, and its K-injective normalization agrees by step 4. The other cited nodes supply invertible o and b. Elementary categorical cancellation therefore gives invertibility of the specified pro-etale gamma. I did not claim alpha itself is invertible: for a noncartesian square it can project away a nonzero complementary component. "Every comparison in this equation" refers to o and b, as actually present in the equation.

I tested the empty V and empty S cases (extension from the empty site is zero), empty complementary component (projection is identity), the refinement V=S,r=id (projection onto the clopen section), both kinds of identity square, and the zero ring (all module sections zero). The formulas still type-check and give the claimed normalization. The argument uses no uniform lower bound over a family or unrelated scalar ring. All seven proof steps are under 2000 characters; none hides a long comparison assertion. Citations.json supplies an unedited full-statement quote for every step/node pair. I corrected no source statement and introduced no statement weakening.
