## Files written

- `dag/nodes/sec-six-functors/lem-coef-derived-tower-counit-projections.json`: statement node, now split in seven steps; not a Mathlib leaf. The statement and original metadata are unchanged, inherited Mathlib searches retained, and eight actual Q138 searches appended.
- `citations.json`: ten step/node entries, each quoting the cited statement verbatim.
- No new nodes, no new Mathlib leaves, and no unit-file changes.

## Attachments

None. I searched `lean/WeilConjectures/` for the exact blueprint tag and the derived tower, constant/limit adjunction, counit/projection terminology. The generic adjunction infrastructure in `CategoryTheory/DerivedCategory/Adjunction.lean` does not state this tower specialization with every normalization and parameter-naturality clause under the item's hypotheses. It also introduces flat-resolution hypotheses for its general left-derived construction that are not needed here.

## WANTED

None. All sources used are available locally.

## Audit and changes

The item was an unsplit extraction, with no attempted proof to retain. Its statement is correct as written; no STATEMENT-DISPUTED repair is needed. The delicate point is that the derived category of strict towers must be retained throughout. I did not identify it with a category of towers of derived objects or use evaluation as a full or faithful functor. I did not assume countable products exact, termwise injectivity of a K-injective tower resolution, or K-injective resolutions of all complexes in the base category.

The proof constructs the derived Hom bijection directly using existing generic nodes. In particular, the exact constant functor makes termwise limit carry K-injectives to K-injectives; this is the reason Hom into the base-category limit may be computed in the homotopy category. The counit is computed as the transpose of the identity, not inferred solely from its evaluations. Its evaluated formula then establishes both resolution independence and the specified normalization. The last step is an explicit naturality equation in the derived tower category.

I read the chapter and unit records and the three blueprint levels in SETUP.md. The current main-20261015 blueprint source for the nearest ancestor is `literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-sp-tower/prop-coef-integral-dualizing.proof.md`, paragraph 2 (third mapping comparison and the final assertion about the specified natural maps). Its physical path differs from the older imported unit path; I retained the item's assigned chapter/unit and blueprint ancestor. The split is a generic homological-algebra ingredient of that comparison, not a new geometric route. Off-unit generic tools are declared in `split_report.tool_uses`.

## Not duplicates

No new nodes were created. Existing generic nodes were reused after searching the whole DAG for the relevant Stacks tags, K-injective Hom and adjunction names, and using blueprint_refs.py searches for derived adjunction, constant tower, inverse limit and K-injective. The specialized site/module sequence adjunction `lem-coef-sequence-projection-derived-adjunction` has different hypotheses (a ringed sequence site); it is not applicable to an arbitrary abelian category, so this item is not an attachment or a duplicate of it.

## Mathlib searches

The eight Q138 requests and their actual results are in searches.jsonl and copied literally into the item's search entries. Both phrasings were read. LeanSearch and LeanFinder were available. The closest hits were `CategoryTheory.Limits.constLimAdj`, read at Mathlib/CategoryTheory/Limits/HasLimits.lean:593–602, and the derived counit construction/formula in Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean:119–133. These supply the ordinary adjunction and an abstract derived comparison formula; they do not by a one-line specialization establish the entire K-injective resolution normalization plus the projection and parameter-naturality clauses. The split performs those comparisons explicitly. Loogle's second request returned no hits and the second source grep returned no hits; neither is recorded as a service failure. Earlier searches inherited from Q63 remain untouched.

## Review by Q138

I read Stacks derived.tex at Tags 0FND (lemma-pre-derived-adjoint-functors-general), 09T5 (lemma-derived-adjoint-functors), 070I (lemma-K-injective), 08BJ (lemma-adjoint-preserve-K-injectives), 070K (lemma-enough-K-injectives-implies), and 070Y (lemma-K-injective-defined), together with sites-cohomology.tex Tag 0941 (lemma-derived-limit-is-ok). The latter is used only as a tower-model reference: its sheaf hypotheses are not imported into the arbitrary-abelian-category argument. The proof origin is marked agent because the strict-tower counit calculation and functoriality expansion are written here from those general results. There are no new node sources to audit.

For step 1 I opened `lem-weil-tower-category-levelwise-abelian`, which states levelwise short exactness and exact evaluation, and `lem-weil-pbc-exact-functor-derived-factorization`, which states quasi-isomorphism preservation and the natural identification with termwise application. The latter is applied only to the exact constant/evaluation functors, not to limit. I also opened `lem-weil-pbc-termwise-adjunction-homotopy`: its statement gives the homotopy adjunction and its actual termwise counit. The ordinary constant/limit adjunction and additivity of limit are written out from the universal property instead of being hidden as a new node.

For step 2 I opened `lem-weil-pbc-right-adjoint-preserves-kinjective`: it requires an additive adjunction and an exact left adjoint. Step 1 verifies precisely these hypotheses for limit and constant towers, so its conclusion applies to LI without assuming anything about the individual I_n. I opened `lem-weil-pbc-kinjective-total-derived`: it provides the natural derived comparison and its isomorphism on K-injectives, assuming the tower category has resolutions, exactly a hypothesis of the item. The exactness needed here is triangulated exactness of QL on the homotopy category; an additive functor preserves cone/shift formulas, as written in this step, so abelian exactness of limit is not being assumed.

For step 3 I reopened the full statement of `lem-weil-pbc-kinjective-hom-derived`: it gives the Hom bijection for every source complex and a K-injective target in any abelian category. It is applied first with target LI and then with target I; step 2 and the chosen resolution establish the respective K-injectivity hypotheses. The termwise-adjunction node gives the middle Hom bijection and its explicit ordinary transpose. Each arrow of the displayed bijection thus has its actual hypotheses verified. Neither K-flat resolutions nor monoidal structures are used.

For step 4 the same Hom bijection gives a unique homotopy class representing an arbitrary derived morphism between two K-injective tower complexes. The natural-transformation clause of `lem-weil-pbc-kinjective-total-derived` supplies the exact equation comparing RL(b) with L(a). The equation for the ordinary counit is the adjunction naturality from step 1. I checked the direction of every map: rho_q goes from RL(B) to QLI, while Q(a) goes from QI to QI'. These equations give the displayed naturality formula and, at b=identity, resolution independence. `def-weil-abstract-derived-category` states the localization property needed to pass source naturality from chain maps to arbitrary derived morphisms, without assuming resolutions in the base category.

For step 5 the unit and counit are defined by the two Hom bijections. Their two formulas and triangular identities follow by substitution, so this is an elementary step using earlier proved steps, not an invocation of an uncited derived-adjunction theorem. For step 6 I checked epsilon_QI composed with Delta(kappa_I) equals Q(gamma_I), and that for a general resolution the inverse of Qq is on the target side. Applying evaluation gives exactly (Qq_n)^(-1) Q(p_n) rho_q. The invertibility of Qq_n follows from exact evaluation in step 1. Resolution independence was proved before making this identification, so there is no circular assertion that the maps are canonical. For step 7 both arrows in the naturality square are morphisms in D(T); its equation uses only counit naturality, functoriality, and lambda's naturality, followed by the already proved projection formula.

I checked sections B–E of delivery-errors point by point: statements introduce all objects and retain their hypotheses; sources have tags and labels; there is no new statement-only node to duplicate or to hide a clause; every non-elementary input is the statement of a cited node; no proof-only construction is borrowed from a cited node; all cited node files were opened and the quotations are verbatim. No node with narrower site, module, bounded-below or exact-product assumptions was substituted. The added proof-dependency set is exactly the union of the step citations. Every step is below 2000 characters; the substantial steps carry the argument instead of delegating clauses to restated nodes.

I tested zero complexes/towers (all maps are uniquely zero), a constant tower (the ordinary counit is the identity under lim Delta = id), towers concentrated in degree zero (the formulas are the ordinary limit projections whenever the chosen complex itself is K-injective), and two resolutions of the same complex (the comparison represents the identity in the derived category). These checks preserve the directions of q, kappa and rho. For an arbitrary morphism of towers, the calculation uses the unique homotopy-class lift into a K-injective target, so it is not restricted to literal maps of a preferred resolution. An empty parameter category gives the unique empty natural transformation, while arbitrarily large parameter categories cause no extra limit or smallness assumption. The proof does not assume that evaluation detects a morphism of derived towers.

## Unfinished work

None in the requested one-level split. Existing cited unsplit nodes retain their independent work items. Server dry run and direct delivery are the required validation and finalization steps.

## Validation

The first required server dry run exited successfully with OK at 1ab59e1fb53. A final wording clarification makes explicit that the equation aq=q' is asserted for two resolutions of the same source complex; the general derived comparison equation already handles different source representatives. The final dry run below rechecks this clarification before delivery.
