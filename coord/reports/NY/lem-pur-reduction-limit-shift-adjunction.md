# NY stage-1 delivery: lem-pur-reduction-limit-shift-adjunction

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-reduction-limit-shift-adjunction.json`: existing statement, split into seven steps; no new nodes and no Mathlib leaves.
- `citations.json`: twenty verbatim statement quotations, one for every cited-node occurrence.
- `searches.jsonl`: five actual searches performed through msearch.py; four services, including a second semantic phrasing.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the exact blueprint id and by reduction/shift/adjunction/total-limit terminology found generic shift infrastructure and finite single-coefficient reduction. None states this strict quotient-semilinear system/total-limit adjunction with its specified cone comparisons. The item has no recorded Lean declaration. The upstream master is reference material, not evidence of completion.

## WANTED

None. The required foundational sources are present in `literature/stacks-project/`.

## Corrections and source scope

STATEMENT-DISPUTED: the original phrase “the Roos total-cone model [def-weil-derived-limit]” attributes a functorial chosen model to a definition that expressly supplies only a property of an object together with a distinguished triangle. The failing inference is to extract a functor or a canonical comparison from an arbitrary distinguished triangle: the definition states that compatible morphisms of such limits need not be unique. This is an object-specification error, not a counterexample to shift compatibility. I corrected that phrase to use the already-specified functorial total derived limit on K-injective towers, its Roos triangle in the sense of that definition, and the cochain-cone convention of def-weil-abstract-derived-category. I also named the existing ringed sequence-site definition explicitly. All original geometric/coefficient hypotheses, both ambient unbounded categories, the actual adjunction and both shift-compatibility conclusions are retained. In particular, I added no normalization, constructibility, finite-Tor-amplitude, completeness, boundedness, product-exactness or coefficient-flatness hypothesis.

The source sentence in main-20261015 `fix-prop-coherence.proof.md` describes preservation of tensor reassociation, evaluation, units and counits, but does not prove this specific shift assertion. The proof is therefore marked agent-written. I read Stacks sites-cohomology.tex, labels section-derived-limits/lemma-derived-limit-is-ok (0940/0941), lemma-adjoint (07A6), lemma-derived-pushforward-composition (0D6E), sites-modules.tex lemma-adjoint-pullback-pushforward-modules (03D7), and derived.tex lemma-adjoint-is-exact (0A8D). The precise canonical-resolution shift compatibility is supplied by the existing, stronger DAG theorem lem-weil-pbc-derived-adjunction-shift, rather than falsely attributed verbatim to 0A8D.

The existing chapter/unit binding is retained. The unit sk-thm-sf-compatibility's coefficient clause and its proof require the actual reduction comparisons to preserve adjunction maps. This item proves a foundational compatibility of that actual adjunction. It changes no unit-level route. The recorded blueprint ancestor remains thm-pur-rational-and-qbar-purity, through the two pre-existing intermediate nodes. Whole-blueprint searches for “shift adjunction”, “reduction”, and “Roos” found no blueprint node that states this particular coefficient-system assertion. Existing generic DAG tools are reused instead of creating restatements.

## Not duplicates

No new nodes. In particular, lem-weil-pbc-derived-adjunction-shift already states the needed general ringed-topos derived-adjunction theorem; lem-weil-roos-split-comparison already gives the kernel-to-signed-cone quasi-isomorphism without exact products. The present item is not a one-line Mathlib specialization: the ringed-site realization, actual total-derived composition comparison, and prescribed Roos shift must first be identified.

The five new Mathlib search records are copied from actual `searches.jsonl` tool/query strings. I read the results of both semantic phrasings. Loogle and LeanSearch returned the generic CommShift assumptions, construction and equations. The grep located shift_unit_app at Mathlib/CategoryTheory/Shift/Adjunction.lean:281 and shift_counit_app at :290, and I read lines 250–310. These require an existing adj.CommShift instance; they do not establish that the prescribed reduction/total-limit comparisons have that property. The second LeanFinder query returned underived sheaf adjunctions. The imported searches were preserved; no unperformed search was added.

## Review by NY

I checked the node against the coefficient-comparison sentence just cited, the small ringed sequence-site definition, and the foundational Stacks proofs above. There are no new statements needing separate sources or edge-case tests. I opened and read the statement of every cited node before constructing the citation file. In particular, I rejected lem-weil-derived-limit-roos-complex and lem-sf-strict-roos-derived-limit-comparison as tools here: their exact-countable-products assumption is not available. The split uses the existing split-tower comparison instead.

Step 1 uses def-coef-ringed-sequence-site for the actual site, actual coefficient sheaves, strict transitions and exact restriction U, and lem-weil-pbc-ringed-topoi-module-adjunction for its module adjunction. The projection inverse image really is constant systems, preserves finite limits levelwise, and has inverse limit as right adjoint; the compatible quotient ring maps give the ringed structure. The explicit compatible-family Hom bijection verifies the formulas for p^* and p_*, not just their evaluated objects. The site is small by the fixed small pro-etale skeleton and the countable index category.

Step 2 uses lem-weil-pbc-ringed-topoi-derived-pullback exactly for the flat-term K-flat comparison, lem-coef-derived-system-evaluation-calculus for the actual reduction-system functor, and lem-weil-pbc-derived-adjunction-shift for the allowed shifted K-flat representatives and canonical comparison. The coefficient rings need not be flat over the completion: flat-term K-flat representatives are precisely why the comparison applies. The degree-i differential calculation shows this is the specified termwise reduction shift.

Step 3 uses def-coef-ringed-sequence-site's exact U, lem-weil-pbc-exact-functor-derived-functor's assertion that every complex computes the derived functor of an exact functor, the normalized comparison of lem-weil-pbc-ringed-topoi-derived-pushforward-composition, and lem-weil-pbc-kinjective-shift. The source and intermediate sites are small, their rings commutative, and a is the identity-topos coefficient change. The normalized composition map really is lim j on representatives. Choosing j[r] makes the shift square equal in each degree, so the argument does not assume U preserves K-injectives or infer shift compatibility merely from an abstract functor isomorphism.

Step 4 uses the canonical adjunction in lem-coef-derived-system-evaluation-calculus and the general derived-adjunction shift theorem. Steps 1–3 identified the underlying module adjunction, its derived functors and canonical comparisons; thus this is its canonical derived adjunction, with the prescribed unit and counit, rather than a newly chosen adjunction on the same pair of functors. Both written equations have the correct source and target: the first starts at P[r], and the second at R L(N[r]) and ends at N[r]. These are equations of system transformations, not an appeal to faithfulness of finite evaluation. The general theorem has no normalized-system or completeness assumption, so it applies to every P and N requested here.

Step 5 uses prop-pur-kinjective-resolutions-exist for a tower-site resolution with injective terms, lem-weil-pbc-ringed-strict-tower-homotopy-limit for its total-limit computation, lem-weil-tower-category-levelwise-abelian for the finite-prefix monomorphism, def-sp-injective-resolutions for extending a map across that monomorphism, and lem-weil-roos-split-comparison for the quasi-isomorphism with components (0,i). I checked the finite-prefix orientation: T_n is nonzero at indices at most n, so extending the map corresponding to id_{J_n} to T_{n+1} gives exactly a section J_n→J_{n+1}. This proves the split-transition hypothesis in each cochain degree. Sectionwise products of sheaves exist; their exactness is never assumed. No choice of splitting enters the formula (0,i), which is natural independently of that existence argument.

Step 6 uses lem-weil-tower-evaluation-kinjective and lem-pc-ringed-space-product-kinjective to justify the derived product, def-weil-derived-limit only to identify the Roos triangle, and def-weil-abstract-derived-category for the cone and shift sign convention. I computed both differentials of χ_r(y,x)=((-1)^r y,x); both give (-dy-(-1)^r h x,(-1)^r dx). Its compatibility with (0,i) identifies it with the actual total-limit shift. The product maps act in both coordinates, so the comparison is natural on chain maps; hence it is also natural after passing through the specified derived model. The sign belongs to the first cone coordinate, and not to the finite reduction map.

Step 7 checks r=0, r=1, r=-1, composition of shifts, zero objects, degree-zero coefficients and the empty scheme. The parity identity works for negative integers, and n≥1 throughout. No extra hypotheses arise. Every proof step is below 2000 characters (the longest is 1269), and none hides an uncited comparison: module adjunction, derived functors, derived composition, shifts, existence of resolutions, and kernel/cone comparison are all existing cited nodes. The elementary finite-prefix and sign calculations are written in full.

The generic foundational statements from other units are declared in split_report.tool_uses with their role; I did not edit maintainer-owned tool_uses. This is the use of general tools, not a replacement of the six-functor unit's route. B1–B10 are satisfied without creating nodes; C1–C8 were checked by reading every cited statement and writing verbatim quotations; D1–D5 are addressed by the explicit site/derived-comparison/sign argument rather than moving a clause into a child; E1–E7 are addressed by the hypothesis, type and boundary checks above. No SGA source, compiler, Lake command, live-project write or direct git command was used.

## Unfinished work

None in this stage-1 split. Existing dependencies retain their existing proof status. Server dry run and direct delivery are the remaining mechanical gates, whose results will be recorded below.

## Validation

The first dry run rejected a short quotation for prop-pur-kinjective-resolutions-exist before pushing. I replaced it with the full verbatim statement, including the existence of a K-injective resolution with injective terms.

The repaired dry run exited 0 and printed `OK (not pushed)` at 55c8ccde14: server preflight passed, including the DAG and split checks. The final direct delivery follows the same item and citation files; only this validation note was appended after that dry run.
