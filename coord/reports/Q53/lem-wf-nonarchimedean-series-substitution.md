# Worker report: lem-wf-nonarchimedean-series-substitution

## Files written

- dag/nodes/sec-purity-real-sheaves/lem-wf-nonarchimedean-series-substitution.json: statement, split into eight steps; the current Q153 statement is unchanged.
- dag/nodes/sec-purity-real-sheaves/lem-wf-ultrametric-family-summability.json: statement, Mathlib leaf; arbitrary-index cofinite summability criterion and ultrametric sum bound.
- dag/nodes/sec-purity-real-sheaves/lem-wf-summable-family-regrouping.json: statement, Mathlib leaf; restriction and arbitrary-fiber regrouping in a complete valued field.
- dag/nodes/sec-purity-real-sheaves/lem-wf-nonarchimedean-summable-products.json: statement, Mathlib leaf; multiplication of arbitrary summable families, without a completeness requirement.
- citations.json: the full verbatim statement of each node used by each numbered proof step.
- searches.jsonl: actual msearch.py queries; write_split.py is a sandbox-only JSON-writing helper, not delivered.

## Attachments

None. I searched the entire read-only WeilConjectures source for the item tag and for nonarchimedean/restricted series/substitution. The tag is absent. The nearby PadicAlgCl.summable_logSeries, norm_smallLog_le and smallLog_mul in NumberTheory/Padics/Logarithm.lean are specialized logarithm facts; they do not state this arbitrary-field restricted-series result or its flattened-family summability assertion. I also searched the new-node IDs and the named general summation declarations in the project source. No project declaration supplies an attachment for any of the three new nodes. The exact upstream master is reference material only and was not treated as evidence of completion.

## Wanted literature

None. The blueprint source and the pinned Mathlib source supplying every non-elementary summation fact are available. These are analytic Mathlib leaves, so their sources are exact declarations and generated additive declarations, rather than invented Stacks tags.

## What was wrong or missing

The inherited item had no proof. Its statement already includes Q153's repaired hypotheses, including inner weighted coefficient decay, its bound by s, outer weighted coefficient decay, and G's zero constant coefficient. I preserved all of these. The blueprint's third paragraph says formal identities can be evaluated because all involved series converge, but gives no unconditional summability or regrouping argument. The split supplies that argument below the existing small-log unit, without changing the unit route or the parent theorem.

In particular, the bound by |a_n| s^n alone is insufficient to control the infinitely many tuples of a fixed positive length. Step 5 also uses B_m tending to zero: for each remaining n, one large coordinate forces a small term. The finite boxes then give uniform finite exceptions. Step 6 proves coefficient decay even if rho is not in the absolute value's value group. No point with |x|=rho is selected.

PowerSeries.comp_eval₂ at Mathlib/RingTheory/PowerSeries/Evaluation.lean:199–206 concerns a continuous ring homomorphism composed with evaluation, not formal substitution F composed with G. It also requires topological nilpotence and a linear topology. The multiplicative restricted-series fact at Restricted.lean:75–77 covers only coefficient decay of HJ. Neither is the full item, so the item is not marked Mathlib. The direct coefficient argument in step 2 is short and needs no extra node for that clause.

## What could not be finished

Nothing remains mathematically unresolved in this one-level split. Every new node is a verified Mathlib leaf, stated without its own proof. No Lean was written, compiled, or built. Only the sandbox was edited; delivery uses the required packaging tool.

## Not duplicates

lem-wf-ultrametric-family-summability vs lem-wf-nonarchimedean-series-substitution: the new node is a criterion and bound for arbitrary families in any complete nonarchimedean valued field, with no power series, weights, products, or substitution; the item must prove that its weighted tuple family satisfies the criterion.

lem-wf-summable-family-regrouping vs lem-wf-nonarchimedean-series-substitution: the new node assumes summability and treats arbitrary index maps in complete valued fields. It neither establishes the item's summability hypotheses nor identifies either grouping with a formal composition or an evaluated product.

lem-wf-nonarchimedean-summable-products vs lem-wf-nonarchimedean-series-substitution: the new node multiplies two already summable arbitrary families. It gives no weighted coefficient decay or zero-constant formal-series composition statement.

lem-wf-ultrametric-family-summability vs lem-wf-summable-finite-subset-products: the existing leaf concerns nonnegative real families and products indexed by finite subsets; it does not concern ultrametric sums or a cofinite decay criterion.

lem-wf-nonarchimedean-summable-products vs lem-wf-summable-finite-subset-products: the existing leaf assumes real nonnegativity and sums products over all finite subsets of one index set; the new leaf multiplies two arbitrary nonarchimedean-field families over their Cartesian product.

I searched all DAG nodes by the summation declaration names, cofinite-filter/unconditional-summability wording, restricted-series/substitution words, and the new IDs. Whole-blueprint searches included summable, nonarchimedean, Cauchy, series, regroup, ultrametric, sum of sums, unconditional, summability, and summable products. The broad searches find series-specific and unrelated category/finite-field statements, not these three arbitrary-family facts. lem-dl-a1-formal-exponential-radius uses complex absolute convergence and nonnegative real majorants and does not supply these ultrametric tools. No source has a shared Stacks tag requiring further pairs.

## Review by Q53

I read dag/chapters/sec-purity-real-sheaves.json, dag/units/sk-d-real-log.json, the current main-20261015 small-log section, and paragraph 3 of lem-wf-deep-principal-unit-log.proof.md. The statement kept from Q153 is a precise general justification for that paragraph, not a new route for the logarithm. The argument is marked agent-written because the explicit estimates supplement the blueprint's omitted convergence justification. All new-node ancestry points to lem-wf-deep-principal-unit-log, via this item, at the relevant paragraph. There are no SGA citations.

For the first new leaf I read Nonarchimedean.lean:30–107, including the to_additive annotation generating NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero at the multiplicative declaration's line 104. The finite-exception formulation is exactly convergence along the cofinite filter tested on positive-radius norm balls. I read Ultra.lean:192–200 for the additive nonarchimedean instance and :346–351 for the generated IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg, including its empty-index branch. The leaf specializes this general normed-group theorem to the additive normed group of a field with its given absolute value. The underlying field notion is exactly the definition in def-weil-field, which I opened; the absolute value and completeness are introduced explicitly in the new statement.

For the regrouping leaf I read Constructions.lean:188–243, especially the generated HasSum.tsum_fiberwise at :239–243, and Group.lean:293–303 for Summable.comp_injective and Summable.subtype. Completeness is in scope for these statements. The new leaf assumes a complete valued field, so its additive normed group supplies the required uniform additive-group and Hausdorff structures. It also cites def-weil-field for the field notion, while introducing its absolute value and metric explicitly. Its grouped summability and equality are conclusions of HasSum.tsum_fiberwise, rather than something extracted only from its proof. Arbitrary and empty fibers are permitted.

For the multiplication leaf I read Nonarchimedean.lean:110–141, including HasSum.mul_of_nonarchimedean:126, Summable.mul_of_nonarchimedean:135 and tsum_mul_tsum_of_nonarchimedean:139. I checked Basic.lean:35–57: NonarchimedeanRing requires a basis of open additive subgroups, not a basis of ideals. The absolute value supplies a normed field and continuous operations, and positive-radius zero balls are additive subgroups by the strong triangle inequality. Thus the specialization really applies, even with a trivial norm and without completeness. Singleton multiplication also supplies the scalar multiplication used at the end of the item.

Step 1 uses precisely the criterion and the bound clauses of the ultrametric-family leaf. The metric is the hypothesis's metric, completeness is available, rho and s are positive, and every evaluation term is bounded by a sequence tending to zero. The sum bound applies with C=s, not with an unproved supremum estimate for G(x).

Step 2 uses the coefficient clause of def-weil-formal-power-series, which I opened in full. The maximum estimate is obtained by finite induction from the given strong triangle inequality. Bounding the two convergent real sequences by M>=1 and choosing N makes every degree-k term small for k>=2N. This is a finite coefficient estimate, so it is elementary; I did not create a node restating the product-restriction clause.

Step 3 uses the product leaf's full arbitrary-product summability and sum conclusion, then the regrouping leaf's conclusion for p(i,j)=i+j. The formal-series definition supplies exactly c_k as the finite convolution, not an analytic substitution theorem. The degree fibers are explicitly identified with i=0,...,k, so no infinite fiber is silently treated as finite.

Step 4 is the finite formal coefficient induction from that same definition. The base n=0 is written, the step appends one positive coordinate, and n<=k makes the composition coefficient a finite sum. There is no circular appeal to evaluation or to the item's conclusion.

Step 5 uses only the coefficient hypotheses and elementary multiplicative estimates and finite counting. The threshold epsilon/(|a_n| s^(n-1)) is used only for n>=1 and a_n!=0, so it is positive and defined. Large n are excluded by A_n tending to zero. For each of the finitely many other n, a single large m_j excludes the tuple. The zero coefficient and empty-tuple cases are handled separately. This step has no hidden analytic convergence assertion.

Step 6 applies that finite-exception estimate to the finite degree-fiber coefficient formula and uses the finite strong triangle inequality. It proves weighted coefficient decay directly, including empty fibers. It does not assume rho is a realized norm or use convergence at a fictitious boundary point. The formal-series citation really supplies the finite coefficient convention used here.

Step 7 applies the criterion only after step 5 has established finite exceptions. The regrouping leaf supplies both groupings and their equality, and the formal-series definition/step 4 identifies the degree grouping. The estimate |term|<=|a_n|s^n is explicitly preserved. Step 8 uses the multiplication leaf in an induction with a written singleton base and a bijection between n+1 tuples and a length-n tuple plus one positive index. Reindexing under that bijection identifies the finite-subsum nets themselves, so it is elementary. A second application with the singleton a_n gives the exact length-fiber sum. Step 1 already established the outer evaluation at G(x), closing the final equality without an additional convergence assumption.

I tested the statements on H=0, J=0, constant series, F constant, G=0, n=0, x=0, arbitrary positive radii (including s<1), and trivial absolute values. If G=0 all positive-length tuples vanish and the empty tuple gives a_0. For trivial norms the restricted hypotheses force eventual coefficient vanishing, and the estimates remain valid. For the leaves, I checked empty index sets, finite supports, empty fibers, a non-surjective grouping map and singleton multiplication. The nonnegative C requirement prevents a false bound on the empty sum. Restriction is not assumed without completeness, and multiplication's completeness-free assertion is exactly what its source states.

I checked delivery-errors B–E against the actual files: all new statements introduce their objects, all are proof-free Mathlib leaves, no statement uses a tag as its definition, every cited statement provides the used fact, and each non-elementary step cites those facts. The statement and hypotheses are unchanged; no dispute or weakened conclusion is introduced. There is no hidden large step: the eight texts range from 542 to 811 characters, all below 2000. The only corrections during writing were to distinguish fixed-length decay from the insufficient outer-index bound and to record the exact scope of the misleading formal evaluation candidates. The msearch grep calls scoped to single files print a malformed filename prefix because rg omits filenames for a single input; I read those sources and ran correctly directory-scoped searches as well, and only the correctly scoped results enter the new nodes' search records. Searches in the new nodes are actual logged queries, not fabricated searches.

The first full delivery dry run rejected all three new leaves for having no definition-node citation. I read the candidate group-definition nodes and did not cite the Tate-module, preadditive-category, or ordered-group nodes as definitions of a bare abelian group: none states that definition. Instead I specialized the two additive-group leaves to the valued fields actually used by this item, and all three leaves now cite def-weil-field, whose statement defines precisely a commutative ring with 0!=1 and inverses for nonzero elements. This is a one-line specialization of the same verified general Mathlib declarations, and changes no hypothesis or conclusion of the item. I ran and recorded new field-specific LeanFinder queries for those two reformulated leaves, preserved the prior general searches, and regenerated every citation quote. The eight item steps are unchanged.
