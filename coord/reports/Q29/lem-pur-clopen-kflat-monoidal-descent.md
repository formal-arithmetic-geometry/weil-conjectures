# Stage-1 delivery: lem-pur-clopen-kflat-monoidal-descent

## Files written

- dag/nodes/sec-smooth-purity/lem-pur-clopen-kflat-monoidal-descent.json: statement, now split into seven steps; no Mathlib match for the whole normalized clopen assertion.
- citations.json: 20 citations, one for each step/node occurrence. Each quote is the complete verbatim statement of the cited node, including its hypotheses.
- report.md: this report. searches.jsonl is the actual search-command log; write_split.py is a sandbox-only preparation script, not a project change.

New nodes: 0. New Mathlib leaves: 0. No unit record needs changing: the item is not a unit key statement.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for clopen together with K-flat/monoidal terminology. No project declaration states this item. Existing finite-coefficient upper-star monoidal files concern a more restricted coefficient functor; they do not state the arbitrary ring-sheaf finite-clopen equivalence with all its specified comparisons. No compilation was run.

## WANTED

None. All source material used is present locally.

## Findings and corrections

The imported item has a complete statement and an empty proof. Its statement is retained verbatim. No blueprint_update or released stage-1 repair note is present for this item. No statement dispute was found.

The whole split can use existing nodes. In particular lem-weil-pbc-site-derived-tensor-descent explicitly supplies extension and uniqueness for transformations on the flat-term K-flat subcategory, not merely existence of derived tensor. This avoids silently invoking a general descent theorem without a node. Likewise lem-pur-kflat-total-tensor-model supplies closure of that very resolving class under total tensor on sites; the ringed-space-only lem-pc-kflat-tensor-product would not cover this pro-etale setting.

The ordinary comparison b alone states signed-symmetry compatibility but does not explicitly assert its total associativity and unit compatibility. The proof consequently writes these verifications out on triple and unit generators, using its summandwise formula and the actual constraint formulas. The prescribed derived structure is used throughout; no replacement structure is obtained by abstract transport across the equivalence.

Generic off-unit tools are declared in split_report.tool_uses: lem-weil-pbc-site-derived-tensor-descent, lem-sf-ringed-derived-closed-symmetric-monoidal and lem-sf-ringed-tensor-complex-constraints. They provide localization and the already prescribed constraints, without replacing a step of the purity unit route.

## Searches and Mathlib verdict

Read the inherited search records and retained them unchanged. Ran fresh LeanFinder twice with different formulations, LeanSearch, Loogle, and the required grep command in CategoryTheory. The first Loogle expression used an unknown identifier, which is recorded as a rejected query rather than evidence of absence; a second expression with CategoryTheory.Functor.IsLocalization succeeded. Read all returned hits. In particular, read Mathlib/CategoryTheory/Localization/Monoidal/Functor.lean, including functorCoreMonoidalOfComp and its normalization, and the exact-derived and transported-symmetry source files. These are useful generic infrastructure. They do not by a one-line specialization construct the particular flat-term K-flat model localization, establish the clopen preservation properties, and identify this comparison with the prescribed pure-tensor b. Therefore the item is not a Mathlib leaf.

Ran tools/blueprint_refs.py ancestor for the item and whole-blueprint searches for K-flat, clopen and normalized tensor. The nearest ancestor is def-pur-section-invariant. No imported node states the same normalized arbitrary ring-sheaf finite-clopen assertion. Read both the older ancestor text and its current main-20261015 location under sec-six-functors-basics/sk-def-purity-conv; the final invertibility assertion remains the ancestor place. No new node was necessary, so no statement-only work or fabricated searches are introduced.

## Not duplicates

No new nodes. The existing localization, total tensor closure and native constraint nodes are reused. In particular the ringed-space-only tensor-product node was not duplicated or incorrectly applied.

## Review by Q29

I read the full item and all of its statement dependencies, with particular attention to the three supplied clopen interfaces. I read the chapter and unit records and the three-level restriction in SETUP. The unit is purity conventions, and this item supplies the tensor-calculus tool used below the section-invariant invertibility assertion; none of its coefficient or geometric route is changed.

For the item source I read sites-cohomology.tex at Tag 06YS (lemma-K-flat-resolution), Tag 0G7D (lemma-factor-through-K-flat, including its final flat-terms assertion), the construction preceding Tag 06YU (definition-derived-tor), Tag 07A2 (lemma-tensor-product-K-flat), Tag 0FPQ (lemma-symmetric-monoidal-cat-complexes) and Tag 0FPT (lemma-symmetric-monoidal-derived). The last two omit the monoidal verifications: I have not treated those omissions as proofs of the comparison diagrams. I also read the tensor-sheaf definition and Tag 0G6Q (lemma-tensor-flats) in sites-modules.tex. The normalized clopen application is my argument, so proof_origin.by is agent. There are no new nodes whose sources require a separate review.

Step 1 uses exactly the preservation and chain-map naturality clauses of lem-pur-clopen-total-tensor-kflat-detection, the specified kappa comparison in lem-pur-clopen-unbounded-derived-localization, and the natural computation isomorphisms of lem-weil-pbc-site-derived-tensor-descent. I checked the direction of every arrow in the displayed composite: first invert t, then kappa, then Q(b), then t', then the inverses of the two factor kappas. Restriction preserves both flat terms and K-flatness by the two explicit clauses of the detection node. Each small pro-etale site uses the stipulated universe, exactly the smallness relative to the module universe required in the site-level descent node. No finite-dimensional or boundedness hypothesis has been inserted.

Step 2 applies the final transformation-extension sentence of the descent node with E equal to D(R_i). It explicitly says both existence and uniqueness. Applying it to the inverse model maps and then to their composites proves invertibility and uniqueness, including arbitrary derived morphisms. It does not rely on an uncited choice of roofs or an unstated functorial replacement.

Step 3 cites the site-level flat-term total model lemma for the two iterated models; this is why normalization can be applied to the inner tensors. I read its statement, including arbitrary unboundedness and flatness of the direct-sum terms. The constraint nodes specify unsigned reassociation on every pure triple and localization to the prescribed derived associator. The definition of sheaf tensor as sheafified sectionwise tensor tests equality locally on pure tensors; the universal property of the total direct sum tests equality on its summands. The two composites both send the same triple to the same ordered restricted triple. No assertion that sections of an infinite coproduct are a sectionwise direct sum is needed: the argument is by the coproduct's categorical universal property.

Step 4 uses the signed-symmetry compatibility that the total comparison node actually states and the derived structure node's exact (-1)^(pq) normalization. Both paths have precisely one such sign, retained under the additive restriction functor.

Step 5 uses the ordinary unit compatibility in the clopen tensor statement and the degree-zero coefficient and action formulas in the native constraint node. I checked separately that R[0] is an admissible flat-term K-flat representative: module tensor with R is the identity and complex tensor with R[0] is the identity, so the two definitions of flatness and K-flatness apply directly. Thus unit normalization is not obtained by assuming the coefficient complex has a resolving replacement with an unspecified unit map. Both left and right routes give restriction of the same scalar action.

Step 6 uses essential surjectivity of the equivalence explicitly stated in the descent node. All routes in the already constructed diagrams are natural on the derived categories. Conjugating by isomorphisms from model representatives and cancelling them proves the general three-, two- and one-variable equations. This is an elementary naturality argument with its cited essential-surjectivity hypothesis, not an additional multicategory localization theorem hidden in the word descent.

Step 7 uses only the clopen derived equivalence and its explicit zero-category clauses. Coordinatewise equality is the definition of morphisms in the product. A strong symmetric monoidal functor whose underlying functor is an equivalence is a symmetric monoidal equivalence; no specified monoidal inverse or extra normalization of G is asserted by the item.

I checked B1-B10: no new nodes, statements self-contained and unchanged, one-backslash TeX after JSON decoding, tag/label references, real searches retained with their actual results, no false Mathlib leaf or unsupported attachment, and filled blueprint provenance. I checked C1-C8 by opening every cited statement; citations.json contains their verbatim texts. No proof argument from another node is being cited in place of its statement, no definition is cited as an unproved preservation theorem, and the three generic off-unit tools are declared. I checked D1-D5: seven actual construction/verification steps, no clause copied to a new node, no cyclic helper and no omitted diagram argument. I checked E1-E7: the site and coefficient categories match all tools; iterated tensors stay resolving by the site-level lemma; the comparison is the specified one; signs and actions are written out. Every step has fewer than 1100 characters, so no step crosses the 2000-character review threshold.

Small cases checked: one identity component gives the original comparison; an empty component gives its zero category; zero R forces zero modules and complexes; an empty covering forces X empty; zero input complexes give unique zero maps; R[0] on either side gives the action-unit formula; complexes concentrated in odd degrees produce the same minus sign on both symmetry routes; negative degrees use the same parity convention. Arbitrary unbounded triples are covered because the closure lemma and all direct sums are unbounded, not a bounded truncation argument.

## Unfinished work

None in the split. Required server dry run and push are performed after this review; their results are recorded below when complete.
