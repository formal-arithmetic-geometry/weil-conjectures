# Worker report

Item: lem-coef-sequence-global-sections-evaluation. Group Q11. Stage 1 only.

## Files written

- dag/nodes/sec-six-functors/lem-coef-sequence-global-sections-evaluation.json: split in seven steps, unchanged statement, no new nodes and no Mathlib leaves.
- citations.json: 21 entries, one for every step/node citation, quoting the cited statement verbatim.
- report.md: this report. searches.jsonl is the unmodified msearch log.

There were no earlier node files or report in this item's sandbox. I copied the live item, preserved its earlier search records and blueprint metadata, and appended the five searches actually run in this session. No repository, launcher, Lean source, or unit file was written. No compiler or build was run.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint tag and for sections/tower/evaluation terminology found no declaration covering the whole statement. CategoryTheory.tower_evaluation_isKInjective in WeilConjectures/Algebra/Homology/TowerEvaluationKInjective.lean:34 supplies only the existing generic node lem-weil-tower-evaluation-kinjective. It is not an attachment of this item. The project Sheaf/Paper/CoefDerivedSystemEvaluationCalculus.lean contains related infrastructure, not an eligible whole-item declaration under WeilConjectures.

## Sources and route

I read sites-cohomology.tex, label lemma-derived-limit-is-ok (Tag 0941), especially the proof's exact left adjoint to evaluation, and label lemma-derived-pushforward-composition (Tag 0D6E). I also read lemma-modules-abelian-unbounded (Tag 0D6J) to check the source's explicit comparison via a module K-injective representative followed by a scalar-forgotten K-injective resolution. The combination and coefficient cocycle proof are agent-written and marked accordingly. There is no SGA input.

I read the chapter sec-six-functors and unit sk-prop-sf-biduality-general, the nearest blueprint ancestor prop-coef-integral-exceptional-adjoint and its mapping-complex paragraph. This item supplies the constant-coefficient tower sections needed in that paragraph; it neither proves biduality anew nor replaces its geometric route. The imported source did not supply proof steps. I replaced that gap by the seven explicit steps. The generic tools from other units are declared in split_report.tool_uses for maintainer review, not in tool_uses.

## Mathlib and duplicate searches

I searched the whole DAG by Tags 0941 and 0D6E, by constant-tower and evaluation/K-injective phrases, and read the relevant existing statements. I ran blueprint_refs.py ancestor and searches for global sections, tower, scalar restriction, termwise global, and K-injective. None identifies this entire statement with a blueprint node. The existing general tower evaluation and ringed-topos composition statements are cited directly. No new node was needed, so there are no new/existing-node duplicate pairs.

The five new msearch calls were LeanFinder on derived termwise sections and on a second evaluation formulation, Loogle on CategoryTheory.Functor.IsRightDerivedFunctor, grep on derived/evaluation and KInjective/evaluation patterns in CategoryTheory, and LeanSearch on unbounded sections of sheaf towers. All services answered. The hits concern ordinary sections, evaluation preserving limits, K-injective definitions, abstract Kan extensions, exact derived functors, and bounded/injective-resolution derived functors. I read the Mathlib right-derived universal property and exact-functor localization declarations. These do not construct this unbounded tower-sections functor with both specified coefficient comparisons. The queries and returned names are recorded exactly; no unavailable service was called a negative result.

## What changed and what remains

The statement is retained, including arbitrary commutative ring sheaves, an arbitrary compatible A, unbounded complexes, actual strict tower transitions, and naturality for derived morphisms. Statement dependencies gained the module-sheaf definition and inverse-system definition actually used by its notation. Proof dependencies are exactly the union of step uses. There are no new statements to await a split and no unproved fact hidden in a new node. The cited existing theorem nodes remain whatever their live status is; this delivery is only a one-level stage-1 split.

WANTED: none. Statement disputes: none. Nothing remains unfinished in this one-level split.

## Review by Q11

I checked the statement against 0941 and 0D6E rather than assuming varying-ring evaluation preserves K-injectives. In 0941 the exact left extension is a tower of copies of the same module followed by zeros. This justifies constant-ring evaluation, not varying-ring evaluation. The proof restricts first to A, exactly as the item requests. For the coefficient comparison, 0D6E applies to the identity underlying topos with the ring-sheaf map R to S, followed by the unique geometric morphism to sets with coefficient Z. The target modules are abelian groups; no terminal object of the chosen site is needed.

Step 1 uses the explicit kernels and sheafified cokernels in def-weil-sheaf-of-modules-category, the sectionwise action in def-pc-sheaf-restrict-scalars, levelwise exactness in lem-weil-tower-category-levelwise-abelian, and the exact-localization conclusion of lem-weil-pbc-exact-functor-derived-factorization. Restriction preserves those actual kernels/cokernels, and compatibility of A to B_n makes the transitions A-linear. Each cited statement says precisely that ingredient; none is used to claim preservation of K-injectives by scalar restriction.

Step 2 uses lem-weil-pbc-small-module-diagrams-grothendieck for the entire constant-A tower category, then the general Grothendieck-category existence theorem lem-weil-pbc-kinjective-functorial-existence. The latter really quantifies over arbitrary Grothendieck abelian categories, so it applies to towers. prop-pur-kinjective-resolutions-exist applies to each individual ring sheaf on the same small site. The countable index category is small in the chosen universe. I did not cite the individual-module resolution theorem as if it alone supplied tower resolutions.

Step 3 applies lem-weil-pbc-kinjective-total-derived to the additive sections functor on the homotopy category followed by localization in D(Tow(Ab)). I wrote why this functor is exact on homotopy triangles: shifts, homotopies and cone differentials are preserved, with only finite biproducts. I am not claiming that ordinary global sections preserve short exact sequences. The existence hypothesis is Step 2, and the cited theorem provides both the functor and its universal unit. The tower-category statement supplies the componentwise additive structure.

Step 4 uses exact evaluation from the tower-category statement, the full unbounded assertion of lem-weil-tower-evaluation-kinjective, K-injective computation from the total-derived theorem, and the actual Hom-bijection in lem-weil-pbc-kinjective-hom-derived. The last node explicitly states both bijectivity for an arbitrary source and homotopy equivalence of quasi-isomorphisms between K-injectives; it is not just a definition. Thus arbitrary derived input morphisms may be computed on K-injective tower representatives. Positive indexing differs from natural indexing only by the displayed order reindexing. Actual evaluated resolution transitions give the beta equation, rather than an appeal to faithfulness of evaluation.

Step 5 uses the universal property of the total-derived theorem to construct sigma and its normalization on every complex. The restriction-ringed-topos node supplies the required geometric morphism; it is not used as an acyclicity theorem. The pushforward-composition node explicitly says that g_*j is a quasi-isomorphism for an S-K-injective input and an R-K-injective resolution of its direct image. This is exactly Gamma(j) here. Its normalization therefore proves invertibility of the sigma already constructed, with the same canonical composition comparison. Existence of the needed individual resolutions is the cited small-site resolution theorem, and exact-localization factorization identifies derived restriction with termwise restriction. All rings are sheaves; no constant-ring, finite-ring, flatness or surjectivity hypothesis is imported.

Step 6 uses only the uniqueness of natural transformations out of the total derived functor, which lem-weil-pbc-kinjective-total-derived states as a bijection. I wrote both composites and their common precomposition with eta_T. Thus the identity and cocycle equations follow in a few lines from cited statements, and do not deserve a new node. The restriction definition supplies the canonical composition identification of scalar actions.

Step 7 is the explicit algebraic calculation combining the beta transition equation and the sigma cocycle. The ring map is B_{n+1} to B_n, so the map d has target r_{B_{n+1},B_n}J_n in D(B_{n+1}), as required for the displayed formula. Naturality moves sigma across d, and the cocycle cancels it. This proves the entire transition clause, including iterated maps; no assertion of derived evaluation faithfulness appears. The cited universal-property theorem supplies the natural transformations used in this elementary calculation.

For B to E of delivery-errors: no new-node form issue, invented notion, duplicate, hollow definition, or relabelled clause is present; every non-elementary input has a cited node and every citation was opened. All citation quotes were copied verbatim from those statements. I checked the zero complex, zero coefficient sheaves, identity coefficient maps, non-flat coefficient maps, zero transitions, n=1, and unbounded inputs. The formulas still type-check in words: identity maps give identity comparisons; zero transitions give zero section maps; non-flat maps require only exact restriction and 0D6E, never exact scalar extension. No product-exactness, enough-projectives, boundedness, or epimorphic-transition assumption is used. Every proof step is shorter than 2000 characters, and the only elementary steps are the written unit/cocycle and transition calculations. I found no source error and made no statement correction.
