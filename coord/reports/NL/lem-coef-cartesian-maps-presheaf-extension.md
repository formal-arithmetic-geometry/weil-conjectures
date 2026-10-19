# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-cartesian-maps-presheaf-extension.json`: statement unchanged; seven proof steps; status split. Original provenance, blueprint ancestry and searches retained. Added the classification and category-calculus statement dependencies needed by its notation.
- `dag/nodes/sec-six-functors/lem-coef-parametric-straightening-mapping-spaces.json`: new statement-only node, no Mathlib match. It concerns arbitrary category-valued diagrams and testing categories; it does not assert a presheaf extension, preservation property or uniqueness.
- `citations.json`: verbatim statement excerpts for every use in every item step.
- `searches.jsonl`: actual Mathlib search-command records. Sandbox-local revision scripts are not part of the delivery.

## Attachments

None. Searched the item id, its exact blueprint docstring tag, Cartesian/presheaf extension and straightening/unstraightening under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/`. Hits concern ordinary presheaf Kan extensions, extension by zero and ordinary pro-categories. None states this coherent quasicategorical result. Searched the new parameterized notion there too. Neither the item nor the proposed child has a qualifying project declaration. No master sorry declaration was counted as finished.

## WANTED

WANTED: Gepner–Haugseng–Nikolaus, *Lax Colimits and Free Fibrations in infinity-Categories*, arXiv:1501.02161v3, Section 1.2, Proposition 6.9 and Lemma 9.10, for the item and the new mapping-space node. Read the HTML online, including both proofs. It is not archived under literature/. No Stacks tag states this quasicategorical result.

## What was wrong or needed expansion

The item was an unsplit statement without a proof. The statement is correct; no STATEMENT-DISPUTED correction was required. GHN 9.10 proves the Cartesian case and suppresses the cocartesian calculation as the same argument. I expanded both through a common mapping test. A cocartesian fibration for G is not the literal opposite of the Cartesian fibration for G: that opposite instead classifies G-opposite. Only the *space-valued source* is opposed here, and its class is explicitly normalized back to X.

The source's size conventions need expansion: the testing presheaf Q_C is V-valued and need not be U-valued. The proof works in P_V(A) when applying Yoneda and representable mapping-space tests. It uses the existing universe-inclusion theorem to preserve the given U-small colimits; it does not resize P_U(A) or index a colimit by that large category.

All proof sources are online and unarchived, so proof_origin is agent. I read the chapter, unit, and recorded blueprint ancestor paragraph. This infrastructure remains below paragraph 2 of prop-coef-integral-exceptional-adjoint through the existing presentability ancestry. Neither chapter nor unit is changed. The item has no blueprint_update. Blueprint-wide searches for Cartesian maps, Cartesian fibrations, mapping spaces, straightening and opposite found no imported node stating this fact or the new child; same_as is empty and the exact ancestor/via chain is retained.

## Not duplicates

- lem-coef-parametric-straightening-mapping-spaces vs lem-coef-cocartesian-straightening: the existing statement identifies the infinity categories of fibrations and diagrams with their spaces of maps. The new node adds the C-parameterized comparison using the entire category of edge-preserving functors, as in GHN 6.9's testing-object argument.
- lem-coef-parametric-straightening-mapping-spaces vs lem-coef-cat-infinity-colimits-cartesian-closure: the latter gives absolute exponentials, not the edge-preserving relative subcategories or their comparison under classification.
- lem-coef-parametric-straightening-mapping-spaces vs lem-coef-cartesian-maps-presheaf-extension: the new lemma has no presheaves, extension, preservation or uniqueness in its conclusion. The item's steps prove those assertions rather than invoking another version of them.
- lem-coef-parametric-straightening-mapping-spaces vs lem-cbc-local-weak-equivalence-homotopy-lifting: the numeric text “Proposition 6.9” refers to a different paper (Dugger–Isaksen), not GHN; the existing statement is about local lifting.
- lem-coef-parametric-straightening-mapping-spaces vs lem-coef-simple-inner-anodyne-base-change: the numeric match is not GHN 6.9; the statement concerns inner-anodyne base change.
- lem-coef-parametric-straightening-mapping-spaces vs lem-coef-labelled-spine-prism-horn-calculus: the existing statement is a simplicial horn calculus, not a parameterized straightening comparison. No source tag is shared by these numerically matching pairs.

## Review by NL

I read GHN Section 1.2, Proposition 6.9 and its proof, and all four clauses and the proof of Lemma 9.10. I read the exact statements of all nodes cited by the item's steps, including their hypotheses, rather than taking facts from their proofs. I checked delivery-errors B–E against those statements and the source. No SGA source occurs in this split.

Step 1 uses the existing coherent opposite involution, the mapping complexes of the marked-point model, and the coherent space model. Horn reversal preserves Kan complexes. For Kan L the functor simplicial set Fun(K,L) is Kan by transposing a horn and applying the cited anodyne pushout-product theorem with the monomorphism empty→K. Thus the space model is the full subcategory on Kan complexes in Cat_V, and the opposite restricts to its coherent self-equivalence O. An equivalence preserves existing colimits by the cited represented cocone criterion; existence is given by the space universe/colimit node. Free cocompletion of the one-point category now identifies the colimit-preserving functors O and identity because both take the point to itself. This proves the coherent space-inversion normalization directly in the item. I initially considered a child for this normalization but removed it because it is a short application of existing statements. I changed this step to non-elementary because it combines horn, equivalence, colimit, and free-cocompletion arguments; it is not a one-line definitional calculation.

Step 2 uses space transport for coherent right-fibration representatives and maps, cocartesian straightening and its opposite form for category-valued classification, and the new parameterized comparison for the functor categories and functoriality. Since A is U-small it is V-small, so category-valued classification applies in V. Opposites take the right horn range to the left one. The opposed fibration has class X-opposite; the equivalence proved in step 1 identifies it with X. The target G is unchanged. All represented totals and mapping categories fit in V.

Step 3 takes the displayed parameterized mapping equivalence from the new node, currying from cartesian closure, and Cat-infinity mapping spaces as cores of functor categories from the marked-point model. The coherent mapping bifunctor in space transport supplies Q_C. I verified the remaining short core factorization explicitly: every edge in a Kan source has inverse triangles by outer 2-horn filling; therefore a map from that source to a functor category lands in its core. The same argument for Kan parameters handles whole mapping spaces. Evaluation undoes currying. This is a defining calculation after the non-elementary relative comparison has been cited, not an uncited descent lemma.

Step 4 uses the universe-change statement for the same right fibration and representable. The pointwise-evaluation Yoneda node states evaluation for an arbitrary presheaf Q_C, not just fully faithful Yoneda. It applies in V since A is V-small and Q_C is V-valued. The separate Yoneda/limits node supplies fully faithful Yoneda for Cat_V, converting the equivalence of its represented mapping functors into F(y(a))≃G(a). Naturality in a and its higher simplices is part of the cited evaluation statement.

Step 5 uses the objectwise colimit assertion of the Yoneda/limits node, and the preservation of U-small space colimits under universe inclusion from the universe-change node. A is a small functor-indexing simplicial set and K is U-small, hence V-small. The contravariant-representable mapping criterion applies in P_V(A) even when Q_C is not U-valued. It computes the actual restriction map, rather than an arbitrary equivalence between its endpoints. This avoids an unstated assertion about inclusion of spaces into Cat preserving colimits.

Step 6 applies the same node's mapping-space characterization of a limiting cone. The category-calculus node provides the relevant limits in Cat_V. The mapping formula is natural in X and identifies the comparison map of the precomposition cone. Testing all V-small C is exactly the cone criterion in Cat_V. The empty indexing category gives F(empty) terminal, as required.

Step 7 uses free cocompletion with small source A and target Cat_V-opposite in W. That target has U-small colimits because Cat_V has V-small limits. The cited free-cocompletion statement expressly permits a larger target and identifies entire coherent functor categories. Taking opposites yields the desired restriction equivalence. The two constructed functors preserve the required cones and restrict to G, so both lie in its fiber over G. Its fully faithful transformation-space comparison supplies coherent uniqueness and identification of both models. The classifier and parameterized comparison give the specified action on X'→X by precomposition, and the action on G by postcomposition, with higher simplices retained.

For the new child I compared its statement to every testing-object display in GHN 6.9's proof, not just the proposition's concluding sentence. H and G are arbitrary category-valued diagrams, C is arbitrary, and there is no colimit or representability hypothesis. The product C×E_H is projected to the fixed base, rather than treated as a right fibration. The statement distinguishes spaces of maps from the full relative functor category and includes precisely the coherent comparison needed by step 3. It is a genuine general lemma, not a clause or restatement of the item. It is left statement-only and unsplit.

I checked the item and new lemma on A empty, A a point, X empty, X terminal, X a two-point space, and X=BG for a nontrivial group. At a point both values are Fun(X,G), up to the proved space inversion; the two-point value is G×G and the empty value terminal. A non-groupoid G such as [1] tests the variance: the proof never identifies its opposite with it. In the new lemma H empty and C empty both give the appropriate terminal mapping space; C terminal recovers the ordinary straightening mapping equivalence. No nonemptiness, connectedness or U-smallness of G's values is used.

I ran three kinds of actual Mathlib search and second semantic phrasings, and read the hits. Quasicategory.Basic:34–43 only defines horn filling. FiberedCategory.Cartesian:50–80 and Fibered:49–75 concern ordinary categories with unique Hom-set lifts. StrictSegal and hoFunctor product comparisons concern strict nerves and ordinary homotopy categories. Functor.KanExtension.Basic:45–60 defines ordinary Kan extensions. None is an exact match or a one-line specialization for the child. Additional exploratory searches about opposite spaces are retained honestly in searches.jsonl; Groupoid.invEquivalence and SSet.opEquivalence were read, but no match or leaf is claimed from them.

Every quoted citation is a verbatim part of the used statement. The new node introduces all its objects, has precise source/provenance, contains no proof or proof sketch, and was searched across the DAG, blueprint and Lean source before creation. Each non-elementary item input is named. No proof step is longer than 2000 characters; the largest is the explicit normalization step, under 1700 characters. The chapter, unit, existing dependency nodes, Lean sources and live tools were not edited. No compiler or Lake command was run.

## What remains unfinished

Only the new general parameterized-straightening statement remains unsplit, as required by a one-level split. The item has a complete proof from its cited inputs. The archival copy remains WANTED. Full dry-run validation is recorded below when complete.

## Second reading by NL

- Step 1: checked against GHN Lemma 9.10(3)-(4), GHN Section 1.2, and the cited opposite, marked-point, space-colimit, free-cocompletion, and horn-product statements; the Kan mapping-space argument and coherent space-opposite normalization are valid, and I marked the step non-elementary because it is a multi-lemma argument.
- Step 2: checked against GHN Lemma 9.10 definitions and the dual Cartesian/cocartesian straightening statements; right-fibration opposition reverses the horn variance and only the space-valued source is opposed, so the target G and all universe hypotheses are preserved.
- Step 3: checked against GHN Lemma 9.10 proof's first mapping-space display and Proposition 6.9, with the cited cartesian-closure, core, and transport statements; currying, core factorization for Kan sources, evaluation, and parameter naturality give the displayed equivalence.
- Step 4: checked against GHN Lemma 9.10(1),(3), the universe-change and pointwise Yoneda statements, and the Cat-infinity Yoneda criterion; representable evaluation gives both restrictions to G with the required higher naturality.
- Step 5: checked against GHN Lemma 9.10(2), objectwise presheaf colimits, and universe inclusion; the argument indexes only by the given U-small cocone and correctly permits V-valued test presheaves.
- Step 6: checked against GHN Lemma 9.10(2),(4) and the cited Cat-infinity mapping-space cone criterion; the equivalence identifies the actual precomposition cone, including the empty-index case, so the limit claim follows.
- Step 7: checked against GHN Lemma 9.10(1)-(4), the free presheaf cocompletion statement, and the cited classification/transport statements; uniqueness, transformations, higher simplices, and actions on X and G are all retained.
- New node `lem-coef-parametric-straightening-mapping-spaces`: checked against GHN Proposition 6.9 (proof, including its testing-object calculation) and all cited straightening and cartesian-closure notions; it is a genuine parameterized mapping equivalence, introduces all objects, has no extra hypotheses, and is not a duplicate or restatement.
- Small cases: checked A empty and terminal, X empty/terminal/two-point/BG, G a non-groupoid, and C empty/terminal in the new node; the variance and nullary cases behave as stated.
- Searches: reread the recorded LeanSearch, Loogle/LeanFinder, and Mathlib grep results for the item and child; all matches are ordinary-category or ordinary-presheaf results, so both remain no-match nodes.
- Changes: changed only item step 1's `elementary` flag from true to false and corrected its review explanation; this prevents a substantial horn/opposite/free-cocompletion argument from being misclassified as elementary. No statement, dependency, citation, or source was changed.
