# Worker report

## Files written

dag/nodes/sec-smooth-purity/lem-kun-affine-support-vanishing.json — item split; no new nodes, no new Mathlib leaves. citations.json records every cited statement. Searches were run through msearch.py and retained in searches.jsonl.

## Attachments

None. Searches by item tag, affine support/cohomology terminology, and 0F0W in WeilConjectures found no declaration stating the item. The upstream master is reference only; no sorry declaration is treated as finished.

## WANTED

None.

## Findings and corrections

The item is the separably closed specialization of Stacks 0F0W, etale-cohomology-lemma-interlude-II. Its statement needs no correction. The source leaves the closed-support reduction details omitted; these are now explicit. Rather than create a duplicate support approximation node for 0F0N, the split uses the existing, more directly applicable lem-sc-support-dimension-union. This gives dimension-bounded closed supports, not merely the total dimension bound of T. There is no fixed-exponent or invertibility assumption on the torsion sheaf.

The existing affine torsion cd node is a cited black box; its internal induction uses the support-union lemma, not the present item. Thus this reuse does not introduce a cycle. The unit has no proof paragraphs, while its ancestor lem-kun-0f10 explicitly names the 0F0X affine support route. This split supplies the 0F0W input in that route. Generic tools from the CBC and curve-estimate units are declared in split_report.tool_uses.

## Unfinished

None for this one-level split. Existing dependencies remain available for their own stage-1 work. No Lean was written or compiled, no agent was started, and no delivery was pushed.

## Not duplicates

No new nodes. Blueprint searches for support and support-dimension found lem-sc-support-dimension-union, which is reused. The affine support search found no blueprint node stating this entire item. DAG searches by 0F0W, support-in-subset, closed-supported essential image, affine cohomological dimension and filtered cohomology found all the cited existing inputs.

## Review by NU

I read Stacks etale-cohomology.tex at 0F0W (lemma-interlude-II), its support approximation 0F0N (lemma-support-in-subset), the closed-immersion essential-image proposition 04CA, the affine dimension bound 0F0V, and the fixed-scheme filtered-colimit lemma 03Q5. I also read the blueprint statement and proof of lem-sc-support-dimension-union and the full statements of every node cited in the split.

Step 1 uses the actual statement of lem-sc-support-dimension-union: it gives the canonical colimit of the specified kernel sheaves over closed subsets of dimension at most c. The support definition makes the imported hypothesis exactly its stalk hypothesis. Finite unions and the empty subset verify directedness; the closed subsets form a set, so there is no large-index colimit gap.

Step 2 uses 04CA for its essential-image assertion and for the inverse image being a left inverse, not for an unstated cohomology comparison. The kernel's restriction off Z is zero directly on etale objects of that open. The torsion characterization applies to arbitrary torsion abelian sheaves, so taking subsheaves preserves it by the sectionwise monomorphism. The sheafified inverse-image construction also preserves the local annihilation property. No module coefficient category is substituted for abelian sheaves.

Step 3 uses the quotient-spectrum characterization actually contained in def-weil-closed-immersion. Quotient algebra generators establish finite type, and the single module generator 1 establishes finiteness under def-weil-finite-integral-morphism. The closed-immersion homeomorphism identifies dimensions directly. These are written-out elementary deductions, not new nodes.

Step 4 uses the separably closed point statement together with the two dimension definitions to get precisely the field bound 0. The affine cd theorem requires only an affine finite-type scheme and that field bound, all verified in step 3. Its sheaf is torsion by step 2. The finite-pushforward cohomology statement applies because i_Z is finite, and gives the whole cohomology comparison in every nonnegative degree. I treated the empty closed subscheme separately to avoid any convention about its dimension.

Step 5 checks the qcqs hypothesis through the affine qcqs node and applies the existing filtered-cohomology statement to the directed system from step 1. Since r>c>=0, its degree range applies. A colimit of zero groups is zero. Small cases checked: empty T, zero G, c=0 (closed-point-supported sheaves), nonreduced quotients, and torsion sheaves with no uniform annihilator. The original statement survives all these cases. The searches returned no support-vanishing theorem; LeanSearch was unavailable and is recorded as such. No unrun search is recorded.

Final citation audit: step 2 also cites the direct-image evaluation formula and the etale-open site localization equivalence for its restriction computation; step 3 cites the lft affine-pairs criterion to obtain finite generation of the coordinate algebra from the finite-type scheme hypothesis. I read these statements and verified precisely those clauses.

## Second reading by NU

- Item statement: checked against Stacks 0F0W, etale-cohomology.tex label lemma-interlude-II, and definitions def-kun-support, def-kun-cd and def-sc-etale-torsion-cd; PASS, exactly the separably closed specialization with arbitrary torsion abelian sheaves, affine finite-type T, c >= 0 and r > c. No invertibility or uniform exponent is imposed.
- Step 1: checked the full statement of lem-sc-support-dimension-union against its use with B=T, K=L, N=G and a=c, and read Stacks 0F0N lemma-support-in-subset; PASS. The canonical kernel-system colimit is the cited statement, not a construction borrowed from its proof. The support definition quantifies over some nonzero geometric stalk, so absence from the support implies every such stalk is zero. The finite-union dimension argument and set-sized indexing are elementary.
- Step 2: checked the actual statements of the torsion characterization, sectionwise kernel definition, direct-image evaluation, etale-site localization, closed-subscheme existence, 04CA and the inverse-image stalk isomorphism; PASS after repairs. The restriction map on objects outside Z is the identity. The sectionwise kernel inclusion gives local torsion without assuming F(U) torsion. Stacks 04CA proposition-closed-immersion-pushforward gives the essential image and inverse-image left inverse. Stacks 03Q1 lemma-stalk-pullback (3) gives precisely the stalk comparison now cited to prove M_Z torsion.
- Step 3: checked the closed-immersion affine quotient characterization, finite-morphism definition, finite-type definition and lft affine-pairs criterion; PASS after making the all-affine-opens quantifier explicit. Quotient algebra generators give finite type; the same quotient characterization over each Spec R gives the single module generator 1. The closed-immersion homeomorphism identifies all chains of irreducible closed subsets, hence their dimensions. These deductions are elementary from the cited statements.
- Step 4: checked lem-kun-cd-sep-closed-point and both cohomological-dimension definitions against thm-sc-affine-torsion-cd, read Stacks 0F0V proposition-cd-affine, and checked the full finite-pushforward-cohomology edge-map statement; PASS. The field bound is 0, W_Z is affine finite type, M_Z is torsion, and r>c implies r>dim W_Z and r>=0. The finite-pushforward node supplies an isomorphism in every required degree, with no missing properness or coefficient assumption. Expanded the empty-site sheaf-axiom argument to avoid the empty-dimension convention.
- Step 5: checked the affine qcqs statement and fixed-scheme filtered-cohomology statement against Stacks 03Q5 lemma-colimit; PASS. The index set is directed by step 1, T is qcqs, and r>c>=0 lies in the cited degree range. A colimit of zero groups is zero.
- New nodes: none; no elementary fact, special case, clause restatement, or Mathlib declaration has been promoted to a new node. Independent msearch.py LeanFinder query using geometric-fiber and cohomological-dimension terminology returned eight algebraic-etaleness/cotangent-module statements, none stating this theorem; the actual result is retained in searches.jsonl and recorded on the item.

Small cases: zero G and empty T give zero cohomology directly; c=0 over Spec L requires only positive-degree vanishing, and H^0 is intentionally allowed to be nonzero; a sheaf supported on a closed point in an affine curve satisfies the same bound. The case c=1 permits H^1 but kills r>=2. Nonreduced quotient rings still have cyclic quotient modules and the same closed-subset topology. Arbitrary torsion sheaves, including those without a common annihilator, are covered by the local-section/stalk characterization. No statement dispute found.

Route and circularity: read the unit sk-prop-sf-kunneth-ordinary and chapter sec-smooth-purity records, and the lem-kun-0f10 proof paragraph naming the affine support input. This remains the 0F0W calculation inside the 0F0X route. The affine-cd theorem uses its own dimension induction and lem-sc-support-dimension-union, not the present item; no dependency on this item was introduced. Generic cross-unit tools remain requests in split_report.tool_uses, not maintainer-owned tool_uses. The added inverse-image stalk node is already Lean-closed on slopmaster2. Read-only searches of the source checkout and upstream master found no declaration stating the item; upstream sorry declarations were not accepted as proofs.

Changes made: cited def-pur-abelian-sheaf-kernel for the sectionwise inclusion; replaced the uncited local-lifting assertion for inverse image by the existing Lean-closed lemma-openclosed-stalk-upperstar and the torsion stalk characterization; verified cyclic quotient modules on every affine open, as the finite-morphism definition requires; expanded the empty-site proof; regenerated citations.json with verbatim full statements for every final citation; recorded the independent semantic search. The first worker's report and Review by NU remain intact, and the item's statement and source are unchanged.
