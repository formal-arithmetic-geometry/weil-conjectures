## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-metric-group-quotients.json`: assigned statement, split into nine explicit elementary steps; no statement change and no Mathlib match.
- `citations.json`: verbatim statement citations for steps 6, 7 and 8.

New nodes: 0. Mathlib leaves: 0.

Attachments: none. Searched `lean/WeilConjectures/` for the exact blueprint id, complete metric group and shrinking subgroup terminology, and for complete/quotient and quotient/limit combinations. Read `WeilConjectures/Mathlib/RingTheory/AdicCompletion/Basic.lean`: its representative lifting assumes algebraic adic precompleteness, rather than deriving reconstruction from the item's metric hypotheses, and it does not give the full statement. The parent report also identifies the coset-lifting hypothesis of `Adic/LisseCover/CocycleLimit.lean` as an input, rather than a metric completeness proof. No exact project declaration was found.

WANTED: none. The paper provides the motivating finite-extension continuous-function identity, not a statement of this general theorem. The argument is explicitly marked agent-written, expanding the retained Q120 report argument rather than pretending the general theorem is quoted from the paper.

Problems found: none in the mathematical statement. No hypotheses, conclusion, statement dependencies, inherited blueprint metadata or unit/chapter records were changed. Inherited blueprint ancestry ends at null; `python3 tools/blueprint_refs.py ancestor lem-sfb-complete-metric-group-quotients` returned None. The already precise `from.place` and via list are retained. The unit still refers to its historical master source; I read that source and the current main-20261015 direct-images proof under sec-six-functors-basics, rather than inventing a nonexistent current sec-six-functors path.

Unfinished: none within the requested stage-1 split. This is a natural-language proof, with no Lean writing or compilation.

## Sources and searches

Read Bhatt--Scholze, *The pro-etale topology for schemes*, Lemma 6.8.2 and its proof, printed pp. 58--59, especially the inverse-limit identity for continuous functions on profinite sets. Read the retained metric reconstruction argument in `coord/reports/Q120/lem-sfb-complete-norm-open-test.md` and the statement/proof of its parent node. The present proof works for arbitrary spaces S and does not import the paper's compactness or finite quotient assumptions. The source attribution expressly distinguishes this generalization from the paper's application.

Read `def-kun-subspace-topology` in full, including its actual statement, and Stacks `topology.tex`, `item-induced-topology` in Section 5.1 and the finite-cylinder discussion in `lemma-describe-limits`. I use only the elementary definitions of product and induced topology, not the general categorical limit theorem. The node's statement says exactly that open subsets of a subspace are intersections with ambient opens.

Read the chapter record and `sk-thm-sf-ctf-stability` unit record, the historical unit source, and the current main-20261015 direct-images proof paragraph (3). This item supplies the complete norm test's integral coefficient inverse-limit calculation, remaining below the unit route. It neither substitutes a geometric route nor claims to realize the whole unit.

Every new Mathlib query used `batch2/msearch.py Q88 lem-sfb-complete-metric-group-quotients`; exact queries and actual results are retained in `searches.jsonl` and appended to the item's existing records. All services responded. LeanFinder was tried with both the inverse-limit formulation and the coherent-coset formulation. LeanSearch returned profinite limit reconstruction and quotient completeness; Loogle returned no hits. The first grep found no open-additive-subgroup reconstruction theorem; a candidate-name grep located profinite reconstruction at `Mathlib/Topology/Algebra/Category/ProfiniteGrp/Limits.lean:138,145,153`. I read those declarations and their use of compactness. They do not specialize to noncompact G. Quotient completeness, Haar covering, separating cosets and controlled products from the second query also do not state this theorem. Existing records from Q120 were retained unchanged; this attempt's records are exactly its actual searches.

Whole-DAG searches by statement terms Cauchy, complete metric, translation-invariant metric, shrinking open subgroup, and inverse limits, together with `blueprint_refs.py search` for complete metric, inverse limit, open subgroup and Cauchy, found no exact replacement. The nearby complete-group forgetful-automorphism and Cauchy-realizer statements concern orbit functors and two-sided uniformity, not this additive quotient tower. No helper node was created: each proposed auxiliary fact has its two- or three-line argument written in the proof itself.

## Not duplicates

No new nodes were created. Existing metric-field, matrix-group completeness, profinite integer-tower and orbit-automorphism nodes do not state this item; the inherited `blueprint.same_as=[]` is confirmed by the searches above.

## Review by Q88

I checked the statement against its motivating source and the parent's retained proof. Bhatt--Scholze supplies the finite-extension identity; the present statement is deliberately the larger agent-formulated completeness theorem. I kept all its hypotheses and clauses. I checked the metric really is a metric (not a pseudometric), that the subgroups are additive, nested and metric-open, and that shrinking is the uniform estimate on every member of one U_N. These are precisely what the proof uses. No compactness of G, finiteness of quotients or compactness/Hausdorffness of S enters.

Step 1 is coordinatewise group algebra: compatibility is preserved by operations because the transition maps are quotient homomorphisms. Step 2 uses the given shrinking estimate and positive definiteness, with epsilon=d(x,y) making injectivity explicit. Neither step quotes a hidden structural theorem.

Step 3 chooses quotient representatives and writes the induction giving compatibility for arbitrary m>=n, including the base case. Step 4 obtains pairwise tail differences in U_N using the subgroup property, not an unjustified sum estimate; it then applies completeness exactly as stated in the hypothesis. Step 5 uses openness at zero and convergence to put x-x_m in U_n and adds x_m-x_n. This directly proves the correct quotient value without invoking an uncited theorem that open subgroups are closed. The choice of m>=n is justified by convergence along a tail. Injectivity makes the answer independent of representatives.

Steps 6, 7 and 8 each cite only `def-kun-subspace-topology`. I opened its statement and copied the verbatim sentence saying opens are ambient-open intersections. Step 6 uses it on H inside the product, then computes each inverse image as a finite intersection of open cosets. The openness of a coset is proved by an explicit metric ball, so there is no hidden quotient-topology theorem. Step 7 uses the same definition to make the single-coordinate cylinder an open neighborhood of a; bijectivity identifies its inverse image under h with the relevant coset, and shrinking puts it inside the desired ball. Step 8 checks continuity from S by the preimages of finite cylinders, then composes with the already continuous inverse. Thus the cited definition says precisely what each step takes from it, and all remaining continuity arguments are written rather than attributed to the definition. The citations file has one verbatim entry for each of these three uses.

Step 9 verifies closure of continuous functions under pointwise group operations using the continuity explicitly assumed for G, writes the homomorphism equation at every coordinate, and writes the precomposition equation. These establish both naturality and the actual quotient-projection compatibility, not merely existence of some abstract isomorphism. The inverse commutes as well by uniqueness of reconstructed elements.

Every step is marked elementary because it is a short calculation from definitions, previous steps and hypotheses; the sole existence theorem used is completeness, which is a hypothesis of the item itself. I did not mark the whole reconstruction as a single elementary assertion or move any of its clauses to a new lemma. The nine step lengths range from 252 to 608 characters, all below the 2000-character audit threshold. The review against delivery-errors B--E checked self-contained objects, correct TeX, exact citations, absence of cycles and relabelled clauses, the explicit m>=n induction, no missing limit-completeness hypothesis, and the concrete naturality equations.

Small cases: G=0 gives the singleton limit, and empty S gives singleton mapping groups. Infinite discrete G with every U_n=0 is allowed and gives the diagonal limit. A genuinely noncompact example is G=product over k>=1 of Z, with d(x,y)=2^(-r) for the first differing coordinate r and U_n the sequences whose first n coordinates vanish: a Cauchy sequence stabilizes each coordinate and hence converges, U_n shrink, and the quotients Z^n are infinite. The proof applies unchanged. Dropping completeness would fail for Z with its 2-adic metric and U_n=2^n Z, whose quotient tower has nonintegral 2-adic elements; the retained completeness assumption excludes this counterexample. Dropping shrinking would fail for the constant tower U_n=G on nonzero G; the retained shrinking hypothesis excludes it. Repetitions among the U_n cause no issue, and no strictly decreasing assumption is used.

No repository or launcher file was written, no git command was run in the shared repository, no agent was started, and no compiler/Lake/build tool was used.
