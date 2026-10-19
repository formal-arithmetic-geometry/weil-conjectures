# Stage-1 report: lem-weil-pbc-adic-tor-flat-cohomology

## Files written

- `dag/nodes/sec-smooth-base-change/lem-weil-pbc-adic-tor-flat-cohomology.json`: statement, split; no exact Mathlib match. Eleven proof steps; existing nodes only. Statement and all original hypotheses and conclusions are unchanged.
- `citations.json`: one verbatim statement excerpt for every step/node pair (52 entries).
- `report.md`: this report. `searches.jsonl` is the search command's log; `write_split.py` is sandbox-only preparation code.

New nodes: 0. New Mathlib leaves: 0. No unit file changed: `sk-rem-rest` is a remark with no proof steps, and the item is a refinement of `thm-weil-pbc-integral-truncations`, not the unit's key statement.

## Attachments

None. Searched the project declarations under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by the item id, blueprint tag, and the adic/Tor/flat/cohomology notions. No declaration gives all the equivalences, all supplied models, and the final canonical reduction assertion. The upstream master is only reference material; its sorry declarations are not attachments. The item has no imported closed Lean audit establishing this result.

## WANTED

None. All sources used are already available locally.

## Problems in the imported material

The imported item did not supply a complete argument for the converse from all-level Tor vanishing to flat integral cohomology. The ancestor's flatness/torsion-freeness sketch is insufficient by itself: one must produce finite ordinary DVR models and show that a positive-exponent elementary divisor produces nonzero Tor at some sufficiently deep level. Steps 5--8 give that calculation. The equivalence with *every* supplied local model also needs a complete-object comparison, not merely equality of finite reductions; steps 9--10 provide it with a strict-tower lift and functorial derived limit.

There is no statement dispute and no change to the target's meaning. In particular the base remains any noetherian finite-dimensional scheme with the specified invertibility assumption, not just a finite-type scheme over a field. The constant coefficient sheaf and its completed ring sheaf are kept distinct. The statement's reference to `prop-weil-pbc-levelwise-truncations` is contextual: this proof does not use that proposition as a flatness criterion.

## Source error

Two reused nodes have inaccurate source-place descriptions, rather than false statements. `lem-sc-dvr-saturation-line-smith-normal-form` describes Tag 00PD as a PID structure theorem; the tag file identifies 00PD as `algebra-lemma-characterize-dvr`. The PID module theorem is Tag 0ASV, `more-algebra-lemma-modules-PID`. I read the actual submodule Smith-normal-form statement and its recorded Mathlib source, `LinearAlgebra/FreeModule/PID.lean` around line 492; it is the statement used in step 6. The item's step source uses 0ASV. Likewise the bounded-above-flat K-flat lemma is Tag 06YQ, `sites-cohomology-lemma-bounded-flat-K-flat`; 06YS is the K-flat resolution existence lemma. The item's sources distinguish them. These other nodes were not edited.

A transitive dependency traversal also finds the inherited missing id `def-weil-pbc-etale-morphism` elsewhere in the shared DAG. No step of this delivery directly cites that id. It is reported here rather than repairing another item's files.

## Unfinished work

None for this one-level split. Proofs of the existing cited nodes remain their own DAG work. No Lean was written, no compiler or build was run, and no delivery was pushed.

## Not duplicates

No new nodes, hence no new/existing tag pairs. Whole-DAG keyword and tag searches located the existing completed-coefficient reduction, restriction, perfect-model, Smith-normal-form, K-flat, and complete-tower lemmas, which were reused. Whole-blueprint searches for the id, flat cohomology, all-level higher Tor, consecutive quotient, and Tor compatibility found the ancestor `thm-weil-pbc-integral-truncations` and no separate statement of this full equivalence. Its statement hypothesis paragraph and first proof paragraph are the recorded blueprint place; `same_as` is empty. The remark unit supplies no proof route to replace. Generic off-unit tools are explained individually in `split_report.tool_uses`.

## Mathlib search review

All six entries in `mathlib_searches` were actually run through the prescribed `msearch.py NA lem-weil-pbc-adic-tor-flat-cohomology` command and retain its query text. LeanSearch and LeanFinder returned ordinary flatness criteria, completion facts, and projective-Tor vanishing. Loogle `Module.Flat, IsDiscreteValuationRing` returned no hits. The grep searches in `Algebra/Homology` and `RingTheory/Flat` locate the ordinary module results, not this pro-etale complete constructible equivalence. I read the candidate torsion-free/flat module results in `RingTheory/Flat/TorsionFree.lean` and the Smith-normal-form result in `LinearAlgebra/FreeModule/PID.lean`. These ingredients do not specialize in one line to the item. Two different natural-language phrasings were run. No service failure was treated as absence and no unrun search is recorded.

## Review by NA

I read the item's source, `literature/blueprint/master/blueprint/sec-smooth-base-change/sk-rem-rest/thm-weil-pbc-integral-truncations.md`, including the flatness hypothesis paragraph and the proof sketch, and the neighboring `prop-weil-pbc-levelwise-truncations.md`. The algebra sources checked were Stacks 051K (the Artinian local flatness criterion) and 0539 (torsion-free modules over valuation rings), together with 0ASV (finite modules over a PID). Neither 051K nor 0539 alone states the sheaf-complex equivalence, so neither is used as an unexplained black box. I also read Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11, for the completed restrictions and stratified perfect realization, and the Stacks passages at 093J/093M, 099M/099Q, 09AH, 06YQ/06YS/06YT/06YU, 03EO and 0G7E. There are no new-node sources to review.

For C4 I opened the statement of every node in every step's `uses`; `citations.json` copies their words, not my paraphrases. The checks for the eleven steps are as follows.

1. `lem-weil-l-adic-extension-integers-dvr` explicitly gives the Noetherian DVR/PID structure and uniformizer factorization. `lem-weil-pbc-completed-constant-sheaf-reduction` gives flat completed coefficients and the quotient comparison, so the ordinary two-term resolution remains a resolution over the completed sheaf. `lem-weil-pbc-proetale-immersion-limit-preservation` gives exact inverse image, preservation of limits and the completed-ring comparison for locally closed immersions. `lem-weil-proetale-weakly-etale-localization` identifies the covering object's site with the slice site. `lem-weil-pbc-ringed-topoi-module-pullback-tensor` and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` give the ordinary and derived comparisons for exactly these coefficient-preserving restrictions. Exactness then preserves cohomology and Tor. I do not assume a general inverse image preserves infinite limits.

2. `lem-pc-bounded-above-flat-kflat-site` applies to a flat degree-zero sheaf, and `lem-weil-pbc-ringed-pullback-preserves-kflat` explicitly preserves flat terms; together they justify preservation of flatness. The ordinary tensor comparison from `lem-weil-pbc-ringed-topoi-module-pullback-tensor` identifies restricted tensor kernels. `lem-weil-pbc-noetherian-stratum-detection` detects a zero sheaf on finite stratum covers under the noetherian hypotheses already present. `def-pc-flat-sheaf-modules` asks for an exact tensor functor; `def-pur-sheaf-tensor-product` specifies the tensor. During review I replaced a constant-ring-only sheafification citation by `lem-pc-sheaf-modules-tensor-closed`, whose arbitrary-ring-sheaf tensor--Hom adjunction actually proves cokernel preservation. Thus the kernel test does give flatness over the completed sheaf.

3. The completed-reduction lemma gives the correct quotient resolution, and the K-flat and derived-tensor-descent statements give a valid flat-term representative of K and a balanced tensor computation on this small ringed site. `lem-pur-derived-change-of-rings` identifies scalar extension; it is not used to resolve the wrong variable. `lem-sf-derived-homology-long-exact` gives the displayed quotient/kernel sequence from the explicit triangle. Flatness in the sense of `def-pc-flat-sheaf-modules` kills the right-hand kernel by tensoring the actual injection on the coefficient sheaf. I wrote the cocycle formula for the canonical map and its quotient compatibility, rather than only claiming the objects are isomorphic.

4. The flatness and tensor definitions justify the explicit balancing isomorphism and preservation of injections after scalar restriction. The bounded-above-flat K-flat lemma makes a flat degree-zero sheaf a valid first-factor representative, and the derived-change-of-rings lemma computes its reduction with no negative cohomology. This proves all positive Tor vanish and the final finite-level flatness, without presupposing a Tor criterion for flatness.

5. I checked all hypotheses of `lem-weil-pbc-integral-stratified-perfect-characterization`: finite coefficient extension, noetherian finite-dimensional T, invertible prime, and membership including the compatible witnesses. Its implication (i) to (ii) really supplies finite projective ordinary A-complexes on a finite stratification with pro-etale covers. The completed-reduction lemma identifies their reductions with the ordinary finite quotients. The restriction argument of step 1 carries the Tor assumption there. The source does not justify replacing arbitrary pro-etale stalks by a conservative family, and this proof makes no such replacement.

6. The Smith-normal-form node states diagonalization for *every submodule of a finite free module*, including a basis of that submodule. This handles the projective terms, the images and the kernels, not only a square matrix over a field. The DVR node gives the unit-times-uniformizer form of each nonzero diagonal coefficient. The downward induction is written out: lift a basis of the last image, split off its two-term complexes and unused last basis vectors, and recurse on a complex of strictly smaller highest degree. The incoming differential lands in the retained kernel because the differential squares to zero. There is no unsupported splitting into cohomology over an Artinian quotient.

7. `lem-weil-pbc-constant-module-section-properties` explicitly says constant sheafification of ordinary Noetherian-ring modules is exact, which transfers the two kernel identities of the displayed periodic resolution. Here the ring is the ordinary Noetherian quotient A/pi^(n+1), not the completed sheaf. `def-weil-pbc-proetale-modules` specifies those finite constant coefficient sheaves. The bounded-above-flat lemma applies to the infinite-to-the-left free resolution. I corrected a potential second-factor gap by citing `lem-weil-pbc-site-derived-tensor-descent` for a flat-term K-flat resolution Q of M and `def-pc-kflat-complex` for the acyclic-cone argument showing Q tensor F maps quasi-isomorphically to M tensor F. This proves that the displayed Tor really is computed by this resolution. With n at least e the first differential is zero on M and the next image is pi M, giving the nonzero residue-field sheaf on each nonempty chart. This directly contradicts the p=1 clause of the actual assumption.

8. After step 7 the local cohomology is finite free, and the tensor definition gives flatness componentwise. `def-pc-flat-sheaf-modules` and `lem-weil-pbc-noetherian-stratum-detection` are exactly the properties needed for the step-2 kernel descent. No extra geometric assumption enters. This proves the converse rather than replacing it by a new node.

9. `def-weil-pbc-bounded-constructible-tower` supplies bounded complexes with adic-lisse terms, and `def-weil-pbc-adic-lisse-module` gives the locally inverse-limit description of each such term. `lem-weil-pbc-torsion-limit-sheaf-completeness` explicitly allows local countable torsion limits and bounded complexes on *any* scheme; hence it applies on U without imposing noetherianity or finite type on U. `lem-weil-pbc-constant-completion-equivalence` transfers completeness to the completed category. For K, completeness is part of `def-weil-pbc-bounded-constructible-complete`. The immersion-limit and slice-localization statements give exact product-preserving restriction. `lem-weil-proetale-countable-products-exact` and `lem-weil-derived-countable-products-core` justify the termwise derived products. `lem-weil-pbc-ringed-strict-tower-homotopy-limit` gives the natural Roos triangle, so the completion-unit computation survives restriction. This verifies the completeness used in the next step for both objects.

10. The equation in `def-weil-pbc-bounded-constructible-tower` says precisely that the supplied e_n commute with the scalar-extension-plus-normalization transitions. `def-weil-pbc-adic-coefficient-datum` supplies strict reduction-tower objects for both complexes. `lem-weil-pbc-sequential-tower-evaluation-full` applies on the small site of U, with the same completed ring sheaf, and states both existence of a lift and its being an isomorphism when all levels are. I use no uniqueness. The strict-tower derived-limit lemma supplies an actual exact functor, so it sends this isomorphism to an isomorphism. `prop-weil-pbc-koszul-reconstruction`, with completeness verified in step 9, identifies each limit with its original object. Thus every supplied L has the required cohomology, not merely the perfect model chosen earlier.

11. The two constructibility definitions ensure at least one supplied model system exists. The comparison just established applies to every such system. Preservation and descent of flatness from step 2, with the stated finite-stratum detection lemma, give both directions between (b) and (c). The concluding reduction assertion is already proved in steps 3--4, so it adds no unproved inference.

I checked the smallest torsion test e=n=1: over A/pi^2 the alternating resolution has both maps pi and Tor_1(A/pi,A/pi)=A/pi, as required. For e>1 taking n=e still gives Tor_1 equal to the residue field, so finite exponents cannot escape detection by appearing first at a deep level. A single free summand has ordinary free reductions and zero higher Tor; a unit differential is contractible before and after reduction. Shifts only change q, and finite sums preserve the explicit calculation. The zero complex, empty strata, and empty scheme are all vacuous cases; nonzero residue-field sheaves are used only on nonempty charts. These tests leave no missing hypothesis or disputed clause.

For the remaining B--E checks, the only delivered node preserves its self-contained statement and definition dependencies; no new node hides a clause or elementary consequence. Proof dependencies are exactly the union of step uses, and a transitive traversal found no path back to the item. TeX was checked after JSON decoding, including for accidental control characters. Sources are tagged by their actual labels; the PID and K-flat tag corrections are reported above. The dry run below is the required tool check; no compiler or manual git command is involved.

## Dry run

`python3 /home/ubuntu/weil-launcher-nt/deliver.py NA lem-weil-pbc-adic-tor-flat-cohomology --no-push` printed `OK (not pushed)` and `preflight passed` (first dry-run commit `355965f401`). The final invocation includes this result in the report. The sandbox contains the accepted split for the second reader; nothing was pushed.

## Second reading by NA

I reopened the item statement and every proof step, then checked each cited node's statement verbatim through `citations.json` and the current DAG. The verdicts are:

- Step 1: checked the DVR resolution, coefficient-limit restriction, slice localization, and ordinary/derived pullback statements; all hypotheses and the claimed restriction of cohomology and Tor are present.
- Step 2: checked K-flat pullback, tensor-kernel comparison, stratum detection, and the closed tensor-Hom adjunction; the kernel argument proves exactly the stated sheaf flatness criterion.
- Step 3: checked the finite-free quotient resolution, long exact cohomology sequence, flatness definition, change of rings, and K-flat tensor descent; the displayed canonical reduction map and its kernel vanishing are justified.
- Step 4: checked balancing over the quotient ring and bounded-above K-flatness; the elementary base-change calculation proves both finite-level flatness and all positive Tor vanishing.
- Step 5: checked the integral stratified-perfect characterization and completed-constant reduction statements against their hypotheses; the perfect local models supplied here are legitimate on the stated finite stratification.
- Step 6: checked the Smith-normal-form node and DVR factorization; the downward induction explicitly splits image, kernel, incoming differential, and unused summands, with no unstated splitting over a quotient.
- Step 7: checked constant-module exactness, K-flat descent, the K-flat cone argument, and the two-periodic quotient resolution; for every positive exponent the computed `Tor_1` is the nonzero residue-field sheaf on a nonempty chart.
- Step 8: checked the finite-free/contractible decomposition and stratum detection statements; the conclusion that model cohomology is finite free and hence flat is valid, including the empty-base case.
- Step 9: checked adic-lisse inverse-limit completeness, constant/completed comparison, exact restriction, product exactness, derived products, and the Roos tower statement; no noetherianity or finite-type hypothesis was added to a covering object.
- Step 10: checked normalization compatibility in the tower definition, the sequential evaluation lift, derived-limit functor, and Koszul reconstruction; only existence of a tower lift is used, and the resulting local comparison is an isomorphism.
- Step 11: checked the two constructibility definitions and the stratum-detection lemma; it gives both directions of (b)–(c), while Steps 3–4 supply the final reduction and flatness clauses.

There are no new nodes in this split, so B1–B7 and the new-node search requirement were checked as vacuous; all reused nodes were searched by id and by the relevant Tor, flatness, Smith-form, completion, and tower terms. I tested the edge cases `n=e=1`, arbitrary `e` with `n\ge e`, a free summand, a unit differential, zero complexes, empty strata, and the empty scheme. No statement dispute or missing hypothesis was found.

Changes made in this second reading: added this node-by-node audit required by the delivery contract; corrected no mathematical content because the item and its citations already agree with their sources. The existing source-place caveats for Tags 00PD/0ASV and 06YQ/06YS remain recorded in “Source error”; no source node was rewritten. The required dry run was rerun after this addition and must pass before delivery.
