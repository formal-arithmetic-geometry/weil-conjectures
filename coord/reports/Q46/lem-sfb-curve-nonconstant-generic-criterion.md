# Stage-1 report: lem-sfb-curve-nonconstant-generic-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-nonconstant-generic-criterion.json: split statement, five proof steps. All original clauses and hypotheses retained. Its Mathlib search candidates do not state the whole item.
- citations.json: verbatim statements for each step dependency.
- searches.jsonl: actual msearch.py output records; prepare.py: sandbox-only JSON preparation.

No new nodes and no new Mathlib leaves. No Lean written or compilation run.

## Attachments

None. Searches for the blueprint tag and for nonconstant/generic-point notions in lean/WeilConjectures found no declaration giving the whole item. In particular, the project reduced-source factorization declaration states an ingredient, rather than the criterion. Mathlib genericPoint_eq_of_isOpenImmersion assumes an open immersion, and RationalMap.ofFunctionField constructs a rational map; neither attaches the item. IsDominant and isDominant_iff only express dominance.

## WANTED

None. All sources used are present.

## Corrections and route

The item was statement-only. No statement error was found. The expression kappa(y)=k is interpreted through the structural field isomorphism, as the cited closed-point node explicitly states. The source 0BY1 treats maps of nonsingular projective curves; the item's arbitrary integral source requires writing out the continuity/dimension argument and reduced-source factorization instead of appealing to that theorem as if it had the item's hypotheses. The proof is accordingly marked agent-written expansion of the source.

I read the current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. Clause (3) gives the direct-image context of the inherited auxiliary alteration argument. The current blueprint does not contain this lower-level generic-point lemma. blueprint_refs.py ancestor prints None for the item: the inherited created.item chain has no identifiable blueprint ancestor. The existing precise from.place and via chain are retained, and same_as is [] after searches for generic point, nonconstant and nonconstancy. No unit or chapter route was replaced.

## Not duplicates

No new nodes. Existing rationality, reduced-source factorization, scheme sobriety and function-field nodes are reused rather than duplicated. DAG searches included 0BY1, nonconstant, singleton images, closed-point residue fields, generic-point specialization, finite extensions and Zariski's lemma; blueprint_refs searches covered generic point, nonconstant and nonconstancy.

## Review by Q46

I read Stacks curves.tex, Tag 0BY1 (theorem-curves-rational-maps), including the definition of constant before the theorem and its third proof paragraph. The missing justification there is exactly what this item supplies. For the rational point and factorization I read schemes.tex Tag 0356 (lemma-map-into-reduction) and the residue-point discussion around Tag 01J9 (lemma-characterize-points), and morphisms.tex Tags 01TB (lemma-jacobson-finite-type-points) and 01TF (lemma-closed-point-fibre-locally-finite-type). I opened every cited node's statement and copied its actual text into citations.json; no citation relies on an internal proof construction.

Step 1 uses the definition of a generic point, scheme sobriety and the definition of topological Krull dimension. Their statements provide respectively closure of a singleton, uniqueness of its generic point, and the forbidden length-two chain. If z differs from y in the closure of y, equality of their closures would contradict uniqueness of generic points; equality of the closure of y with C would force y=eta_C. Continuity then places the whole image in the singleton. This is a short topological argument, not a separate new theorem.

Step 2 uses def-sc-curves for finite type and lem-weil-pbc-closed-point-residue-field-base for the structural isomorphism k -> kappa(y); closedness was proved in step 1. It also uses the spectrum, residue-field and closed-immersion definitions. The residue-field point is explicitly constructed by A -> A/m on an affine neighbourhood; the affine criterion verifies that it is a closed immersion, and the inverse structural field map gives the k-section. The displayed map Spec(a^{-1}) has the right contravariant direction. This supplies the missing scheme structure, not merely the singleton image.

Step 3 uses the equivalence in def-pc-integral-scheme to obtain reducedness, and the exact factorization clause of lem-weil-pbc-reduced-source-factors-through-closed-subscheme. The hypotheses are a reduced source and closed immersion containing its image, both already established. The over-base definition then forces the intermediate map v to equal s_T. There is no finite-type, quasi-compactness, smoothness or properness assumption on T. I also inspected the existing source theorem IsClosedImmersion.existsUnique_fac_of_range_subset_range in the project; the DAG citation itself states the required result.

Step 4 uses the residue-field maps supplied in def-weil-residue-field and their structural compatibility from def-weil-scheme-over-base. Their composite is identity for a section. Injectivity of a field homomorphism then proves the intermediate extension equals k. Clause (a) of lem-kun-closed-point-field says a point of a finite-type scheme is closed iff its residue field is finite over the base. That is precisely the direction used; the separably closed clause (b) is not used. A closed generic point would make C a singleton, contradicting its dimension one, directly from the two cited definitions.

Step 5 uses only the integral-scheme clause of lem-sc-rational-functions-generic-stalks, which explicitly makes the generic stalk a field even for arbitrary integral X. def-sc-function-field explicitly includes arbitrary integral schemes, so k(T) is available although T is not assumed a curve. The scheme local-ring homomorphism is explicitly part of def-weil-residue-field; the stalk definition supplies the description by germs. The k-morphism definition gives k-linearity. Injectivity is proved by the inverse-of-a-nonzero-element argument, not by invoking an uncited dominance theorem.

Edge cases checked: T=Spec k gives the constant branch; T=Spec k(C) with its generic-point map gives the nonconstant branch, and shows why T must not acquire a finite-type hypothesis. The identity of C and Frobenius in positive characteristic give the generic branch without requiring separability. The empty source is excluded by integral, and dimension one excludes a one-point target. A nonreduced source could carry an infinitesimal nonconstant map with singleton image, explaining why the reduced-source hypothesis is essential. Smoothness and algebraic closedness remain as given; the proof uses algebraic closedness exactly for rationality. None of the five steps exceeds 2000 characters, and no new clause-restatement or hidden comparison lemma was introduced.

The item retains all inherited fields and search records. New searches were actually run with msearch.py, including a second semantic phrasing; the hits were read. Generic-point open immersions, dominance definitions, and rational-map construction results require different hypotheses or give fewer clauses and are not Mathlib matches. Off-unit scheme-topology and function-field statements are explicitly declared as generic tools in split_report.tool_uses.

## Unfinished work

None in the one-level split. Independent maintainer review remains the normal next stage after delivery.
