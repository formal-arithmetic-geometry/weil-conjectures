# Stage-1 report: lem-coef-enriched-sequence-projection-formula

## Files written

- dag/nodes/sec-six-functors/lem-coef-enriched-sequence-projection-formula.json — existing statement, split into six steps; not a Mathlib leaf. The statement, its hypotheses, provenance and inherited searches are retained.
- citations.json — 19 step/node pairs with verbatim statement excerpts.
- report.md — this report. searches.jsonl is the search command's log; write_split.py is an item-local writing script.

New nodes: 0. Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures/ for the exact blueprint tag, enriched sequence adjunction and sequence projection wording found no declaration stating this item. The nearby derivedHomRightDerivedLowerShriekIso in SixFunctors/Etale/Derived/TensorHom.lean compares geometric exceptional/direct images, not this varying-ring sequence adjunction and its actual finite projections. The exact sequence-adjunction node names were also searched in both project source roots, with no hits.

## WANTED

None.

## What needed repair

The item was statement-only. Its source cites the adjunction and derived-composition foundations, but those tags alone do not prove the component formula. The split now computes the actual projected morphism by naturality, evaluates the specified system transpose, uses two bijections to obtain uniqueness, and checks the internal, global and degree-zero formulations. No statement correction or route change was necessary.

The sandbox initially had no node, report or search log. I copied the live item, preserving all six inherited Mathlib searches and its blueprint provenance. I ran two further semantic phrasings, LeanSearch, fully qualified Loogle and Mathlib grep through msearch.py; read their hits and the relevant Adjunction/Basic.lean and Enriched/FunctorCategory.lean declarations. homEquiv_counit gives only the ordinary adjunct formula. The enriched functor-category projection is a projection from an end, not the strict derived sequence category with varying coefficient rings. The ModuleCat hits are underived; the light-condensed hits concern another category. No hit states the complete item or a one-line specialization of it.

The whole-blueprint searches for enriched sequence, enriched adjunction, coefficient adjunction and scalar extension found no equivalent imported statement. The broader projection search also exposes geometric projection-formula nodes, which do not identify this enriched reduction/limit projection. No replacement or duplicate node was introduced.

## Tool uses

The split_report declares four generic off-unit tools: lem-weil-pbc-ringed-topoi-derived-tensor-pullback supplies the strong tensor comparison; lem-pur-sheaf-ring-derived-coefficient-adjunction supplies the general sheaf-ring extension/restriction bijection; lem-sfb-dc-hom-scalar-adjunction supplies the evaluation-normalized internal scalar isomorphism; lem-pur-rhom-global-sections supplies the H0 identification. These serve the sequence calculation as black boxes and do not replace the unit's geometric route. In particular the pro-etale-specific lem-weil-derived-scalar-extension-restriction-adjunction would not apply to arbitrary A and B_n, so I used the existing general sheaf-ring lemma instead. I checked dependency reachability for all four tools and the closed-structure node: none reaches this item.

## Not duplicates

No new nodes were created; there are no new/existing tag pairs to distinguish.

## Review by NV

I read the stage-1 brief, stages/1-dag.md, the three blueprint levels in SETUP.md, GOAL.md, the chapter and unit records, and both copies of delivery-errors.md sections B through E. I read the ancestor blueprint's mapping-complex calculation in literature/blueprint/master/blueprint/sec-six-functors/sk-prop-sf-biduality-general/prop-coef-integral-exceptional-adjoint.md and compared the main-20261015 version under sk-thm-sf-package. The current item is a supporting calculation for the first and last mapping-complex comparisons, not the unit's key node, so no unit realization fields were changed. The source route remains fixed.

For the item I read sites-cohomology.tex lemma-adjoint (07A6), lemma-derived-pushforward-composition (0D6E), lemma-pullback-tensor-product (07A4), lemma-internal-hom (08J9) and lemma-section-RHom-over-U (08JA), including their proofs. The first two supply foundations, not a claim that the source literally states this enriched projection formula. The proof is therefore marked agent-written. There are no new nodes requiring separate source reviews.

For step 1 I opened the statements of lem-coef-sequence-projection-derived-adjunction and lem-coef-sequence-pushforward-limit-projections. The former gives the strict K-flat representative and hence e_n R = S_n; the latter gives a natural comparison preserving the actual projections and the reduction unit. Naturality of pi at b and then that unit formula give q_n = U_n(b_n) eta_V. This is the short elementary equality marked as such, not an assertion that evaluations detect equality. The counit and maps are in actual derived categories.

For step 2 I opened lem-sf-ringed-derived-closed-symmetric-monoidal, lem-weil-pbc-ringed-topoi-derived-tensor-pullback, lem-coef-closed-adjunction-enriched-isomorphism and lem-coef-semilinear-derived-sections. Their statements respectively give closed transposition and its evaluation, the canonical tensor comparison for ringed-topos pullback, the exact defining word for b, and preservation of tensor/evaluation/transposition by evaluation. The internal-Hom level formula specifically requires a cartesian first input: the item assumes R P normalized. The second input N is allowed to be arbitrary in that cited formula; the item's stronger normalization hypothesis was retained. No normalization of J and no K-injective preservation by varying-ring evaluation is used.

For step 3 I opened lem-pur-sheaf-ring-derived-coefficient-adjunction and the closed-structure statement. The former applies to the actual map A -> B_n on this small site with no flatness or boundedness hypothesis. The scalar-extension triangle identity converts U_n(b_n) eta_V back into b_n. Composing that bijection with the closed Hom bijection proves uniqueness and the displayed tensor-reassociated formula. This is not a restatement hidden in a new node.

For step 4 I opened lem-sfb-dc-hom-scalar-adjunction and checked its orientation: its stated arrow runs from restricted B_n internal Hom to A internal Hom, so Theta_n is its inverse. The statement explicitly normalizes the transpose by restricted evaluation and the scalar-extension unit. The written evaluation-naturality identity and the projection lemma's e_{N,n} = adjunct(pi_n) then identify the two maps using the same bijections as step 3. The closed-structure lemma supplies the symmetry needed to change left scalar-extension notation to the item's right scalar-extension notation. Nothing asserts that scalar extension commutes with internal Hom.

For step 5 I opened lem-coef-sequence-sections-limit-comparison and lem-coef-sequence-global-sections-evaluation as well as the projection and scalar-Hom statements cited there. The first expressly retains actual finite projections; the second identifies evaluated derived sections with B_n-module derived sections as abelian complexes and is natural in input maps. They apply to J whether or not J is normalized. Thus R Gamma applied to the already proved internal formula, under these specified comparisons, is precisely the global formula, with no arbitrary lift between Roos cones and no independent fiber resolutions.

For step 6 I opened lem-pur-rhom-global-sections and the scalar and projection statements again. The former identifies the two H0 groups with the categorical Hom groups on the stated small ringed sites. The latter two say that the adjunct of pi_n h is e_{N,n} S_n(h), giving exactly the claimed degree-zero formula. This checks both direction and target ring.

I tested the zero first input and zero second input, where all maps under discussion are uniquely zero, and a constant identity coefficient sequence, where the formula reduces to ordinary evaluation/adjunction and h maps to h. For a nonflat coefficient map such as Z -> Z/2, the argument still uses derived tensor and the cited unbounded adjunction, never ordinary exactness of tensor. No assumption of perfection, boundedness or flatness was inserted. The argument obtains equalities from naturality and injectivity of the two adjunction bijections, never from evaluations being faithful. All six steps are below 2000 characters and contain their actual calculations; there is no long inline sublemma to extract.

Against B--E: all notions already have statement dependencies; no new statement, hollow definition or unsplit proof sketch was added. Tags and labels were checked against the source. Every cited node was read for the part actually used, and citations.json copies that part verbatim (C4). All non-elementary inputs have nodes (C1); the remaining projection equality is explicitly calculated. There is no clause-restatement node, no circular dependency, no change of unit route, and no invocation of any SGA source. The authorized work is stage 1 only; no Lean file or shared repository file was written and no compiler was run.

## Unfinished work

None in the one-level split. The cited existing open nodes retain their own obligations for later workers.

## Returned delivery repair: rebase and citation revalidation

The returned delivery is 584a12be36 (return entry 2026-10-21 07:08 UTC). I compared its item and every statement/proof dependency against current server main 099400a2cfaae9ac24af02926da8405c3f9ec603, using read-only server access; the complete comparison is retained in repair-baseline-comparison.json in this sandbox. The saved sandbox statement and six proof steps matched that returned head before repair. The item remains unsplit on current main. Only two cited statements changed: lem-coef-sequence-sections-limit-comparison and lem-coef-sequence-projection-derived-adjunction. Other cited nodes gained reviews, proofs, searches or audit metadata, but their statements did not change. Delivery packaging rebases onto current main and preserves its maintainer-owned metadata.

I reread the entire current sections-limit-comparison statement, not merely the unchanged projection sentence. It now explicitly introduces p as a ringed-topos morphism, specifies K-injective total direct images, quantifies J in the unbounded strict-system derived category, and types R lim on the derived category of strict abelian towers. These are exactly the objects already present in the item: the site is small, A -> B_n is compatible, and J is the system internal Hom. No cartesianness of J is required. In step 5 I now define G by exact restriction U to constant-A towers followed by their total derived global sections, name c_J and the finite comparison kappa_n, and write the actual projection equation pr_n c_J R Gamma(delta) = kappa_n R Gamma(q_n). The finite global-sections-evaluation statement then supplies the comparison with B_n-module sections and its naturality. Applying these to the equality established in step 4 proves the global clause using the current comparison, with no claim about evaluating varying-ring K-injectives. citations.json now quotes the full relevant current formulation, including its construction, quantifier, functor types and projection clause.

I also reread the entire changed projection-derived-adjunction statement. Its mathematical representative is unchanged; it now explicitly cites flat-sheaf modules and sheaf tensor product in the sentence used by step 1. The initial dry run rejected that old quote. I refreshed the quote verbatim and made the one flat-term K-flat representative (Q tensor_A B_k)_k explicit in step 1. This still identifies e_n R with derived scalar extension and adds no flatness hypothesis on A -> B_n. The step's naturality equality and all other finite/internal/H0 arguments are retained.

I rechecked all 19 step/node citation pairs against the current statements and read the other nine proof dependency statements again: the two adjunction bijections, tensor comparison, evaluated internal Hom for a cartesian first input, evaluation-normalized scalar-Hom isomorphism, actual unit/counit projections and H0 comparison still supply exactly the claims recorded in Review by NV. Steps 2--4 and 6 require no repair. The source checks remain Stacks 07A6, 0D6E, 07A4, 08J9 and 08JA in sites-cohomology.tex, which I reopened for this repair. No new node or statement was introduced; the existing search results and searches.jsonl are retained and were reread, so no unchanged search was repeated.

Against delivery-errors B--E I verified the proof still gives an argument rather than new clause nodes; every non-elementary input is cited and each quote is current; all sites/rings and derived categories match; there is no assumption of flatness, boundedness, perfection, normalization of J, or faithfulness of evaluations. Zero inputs, the identity coefficient sequence, and a nonflat Z -> Z/2 map still satisfy the unchanged calculation. Each non-elementary step remains below 2000 characters. The correction concerns proof exposition and current citations, with no statement dispute or route change. All writes remain in the sandbox and no compiler, Lake command or agent was started.
