# Q133 stage-1 delivery

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-continuous-constructible-stratified-lattices.json — statement, split in seven steps; no Mathlib match for the whole statement.
- citations.json — one verbatim statement quotation for each use in every proof step.
- searches.jsonl — actual msearch records for Q133; the item's earlier Q51 searches are retained in its JSON.
- report.md — this report.

Zero new nodes, zero Mathlib leaves. No Lean files were written and no compiler, Lake or build tool was run. Only the sandbox was written.

## Attachments

None. Searched lean/WeilConjectures by the exact blueprint tag and by stratified lattices, lisse lattices, continuous coefficients and module encoding. Existing adic lattice modules concern other coefficients or geometric hypotheses; no declaration gives this item with all its normalization and transport clauses. The relevant DAG encoding nodes are reused as statements, not treated as finished Lean proofs.

## WANTED

None for this delivery. Its mathematical route is documented in the archived Bhatt–Scholze paper and the current blueprint. The existing local-field absolute-value theorem records its own missing textbook reference; this delivery uses that already existing node rather than asserting a new proof of it.

## Problems and corrections

The imported item was statement-only. Its statement is retained exactly: no hypothesis was added and no conclusion removed. The main potential errors were to use an abstract constructible integral model as though it were an embedded lisse lattice, to use etale-only encoding restriction for a closed immersion, or to identify ramified quotient towers at the same exponent. The proof instead uses sk-lem-stratified-lattice, which explicitly gives embedded internal lisse lattices at the fixed E; the actual action/relative-tensor constructions plus general sheaf inverse image; and compatible cofinal quotient powers for ramified coefficient extension.

In particular, lem-weil-pbc-continuous-constructible-integral-stratum and lem-weil-pbc-continuous-lisse-stratified-lattices do not alone assert the embedded lisse lattice needed here. They were read but not cited for that conclusion. No global lattice and no change to a larger coefficient field is introduced.

No source or statement dispute was found. The blueprint's finite lisse partition and invariance-under-nilpotents route is unchanged. Its paragraph 6 is the ancestor of this auxiliary statement, via lem-zl-raw-heart-adic-lisse-stratification.

## Not duplicates

No new nodes are proposed. Blueprint searches for lattice, stratified lattice, continuous coefficient and lisse lattice, and DAG searches by those notions, led to the existing lattice and encoding statements cited below. In particular sk-lem-stratified-lattice supplies the internal fixed-field lattice theorem, whereas this item assembles its application to a constructible sectionwise module with normalized continuous/completed coefficient maps and reduced strata.

## Tool uses

The split_report.tool_uses lists the generic off-unit results. The unit's constructible-to-lisse reduction requires the coefficient, encoding and integral lattice infrastructure; it supplies no replacement proof of that infrastructure. Geometric permanence results establish exactly the finite-type and Noetherian hypotheses those tools require. No step replaces the unit's curve/purity or mixedness route. The maintainer can review the declared tool uses without modifying the unit or chapter.

## Review by Q133

I read coord/brief-stage1.md, stages/1-dag.md, SETUP's three blueprint levels, GOAL.md, the worker role, the chapter and unit records, and both copies of delivery-errors B–E. I read the current main-20261015 proof of thm-zl-real-mixed-by-curves, especially paragraph 6, and Bhatt–Scholze Definitions 6.8.1/6.8.3, Lemma 6.8.2, Proposition 6.8.4 and the first paragraph of Lemma 6.8.13, with Remark 6.8.15. I read the relevant Stacks source at sites.tex Tag 00YV (proposition-functoriality-algebraic-structures-topoi), sites-modules.tex Tags 03EK (section-tensor-product), 03EL (lemma-tensor-product-pullback), and 03D7 (lemma-adjoint-pullback-pushforward-modules); morphisms.tex Tags 01T5 (lemma-immersion-locally-finite-type), 01T6 (lemma-finite-type-noetherian), and the reduction statement cited as 054M. There are no new-node sources to audit.

For step 1, I opened all five cited statements. Finite type over a Noetherian target gives a Noetherian scheme; the minimal-closed-subsets theorem supplies its topological Noetherianity; the immersion theorem gives local finite type; pqf-lem-locnoeth-lft supplies local Noetherianity; permanence supplies composition and separatedness. The subspace ascending-open argument and quasi-compactness are written out so that the theorem on internal lattices is applied only to separated finite-type strata. A field spectrum is covered by its single Noetherian affine open.

For step 2, the absolute-value theorem explicitly supplies the ultrametric inequality, from which the written clopen-ball argument establishes the total disconnectedness required by continuous-coefficient-realizations. That realization statement supplies the actual charts and naturality in a continuous ring map. I checked the completion theorem's displayed evaluation formula: its index n has quotient exponent n+1, so the item exponent n is obtained with index n-1. The immersion-coefficients statement supplies continuous integral completion and localization. The square and uniqueness arguments use their actual inclusion and quotient projections, not an arbitrary coefficient-ring isomorphism.

For step 3, I opened the chart-scheme-naturality and coefficient-pullback-composition statements: they state the chart/pullback square and its composition and coefficient-postcomposition compatibility. The immersion theorem applies to locally closed maps, not merely etale maps. Naturality in A to A' and E to E' supplies finite coefficient extension. In a ramified extension the proof compares compatible ideals/cofinal powers; it never asserts that equal exponents have equal images. Equality in the inverse limit is checked projection by projection, and localization is checked on coefficients and the inverted element.

For step 4, the internal-abelian-sheaf-module equivalence explicitly fixes underlying section groups and restrictions, and the specified encoding fixes actions. I added sk-def-sfb-change-of-scalars and sk-def-sfb-sheaf-tensor because they actually define the internal coequalizer and abelian sheaf tensor; the ordinary tensor definition alone would not justify the internal construction. Thus both sides impose exactly the same balanced relations, making the identity on pure tensors a specified isomorphism. The specialized encoding-scalar-extension theorem confirms the integral-to-rational case. The left-exact-site inverse-image theorem supplies exactness, preservation of colimits, and strong monoidality; def-weil-proetale-inverse-image specifies the scheme site functor and its hypotheses. The argument checks the pulled actions and balancing maps, so it does not borrow a claimed compatibility from the proof of an unrelated node.

For step 5, encoding-local-freeness explicitly asserts the equivalence for any scheme and totally disconnected ring, allows varying ranks and rank zero, and places no nonemptiness restriction on the cover. This justifies inverse-encoding the lisse pieces, without silently changing the local-freeness predicate.

For step 6, sk-lem-stratified-lattice explicitly gives embedded lisse internal lattices, with no field enlargement. The geometric hypotheses are those established in step 1. The embedded-lattice coefficient-comparison statement actually identifies inclusions and scalar-extension pairs and gives the localization formula, including rank zero. Composition of the refinement immersions is the cited permanence clause. The proof then identifies the ordinary rational scalar extension with localization at varpi using the established ring isomorphism, preserving the inclusion map rather than choosing a new isomorphism. This is an application of existing smaller infrastructure; no item clause was relabelled as a new node.

For step 7, the reduction-universal-homeomorphism statement explicitly gives reducedness and the surjective closed immersion with unchanged underlying set. The inverse-image theorem preserves its inclusion and the localization isomorphism; the locally-free-pullback theorem applies to arbitrary scheme morphisms and preserves internal lisseness. Coefficient restriction and step 4 then identify the actual encoded lattice. This proves preservation upon reduction and under further locally closed restriction. It needs no etale assumption and no assertion that reduction is a site object.

I tested the empty scheme, zero sheaf, different ranks on disjoint components, nonreduced strata, the constant sheaf on a point, nontrivial ramification of E and coefficient extension, and the standard nonnormal nodal example where a global lattice need not exist. The proof chooses zero lattices or the empty family where appropriate, retains the actual field E, and only produces lattices stratum by stratum. None of the seven steps exceeds 2000 characters. The routine balancing and inverse-limit calculations are explicit; non-elementary geometric, coefficient, encoding, and lattice inputs are all cited node statements. Every cited statement was opened and copied verbatim into citations.json. A read-only traversal of dependencies found no path from the main coefficient/encoding/lattice inputs back to this item.

I ran the required msearch kinds, with two semantic phrasings, and read all returned hits. They concern generic condensed objects, discrete condensed modules, sheaf equivalences or local generators. I opened the relevant Mathlib Condensed/Explicit.lean, Condensed/Module.lean and sheaf PushforwardContinuous.lean source; these do not give the pro-etale coefficient realization and embedded stratified-lattice statement. The grep hits are unrelated occurrences in isSeparated_iff. The new searches are recorded with their exact query text and actual hit names; no unexecuted query is recorded.

## Unfinished work

None in this one-level stage-1 split. Existing cited unsplit nodes remain in the project queue; this delivery creates none. Server dry-run and final push results are recorded below after they run.

## Validation

The required deliver.py --no-push completed successfully: `OK (not pushed) deliver/Q133/lem-zl-continuous-constructible-stratified-lattices at 85574a0e568: preflight passed`. The server preflight includes check_dag and review_split. This was the sole active dry-run invocation, and it exited before the final delivery command. The final delivery rechecks the submitted report and split.
