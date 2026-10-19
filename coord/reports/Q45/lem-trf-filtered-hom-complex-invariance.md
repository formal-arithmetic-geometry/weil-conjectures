# Q45: lem-trf-filtered-hom-complex-invariance

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-filtered-hom-complex-invariance.json`: item, statement unchanged, split into eight proof steps. Existing searches are retained and fresh logged searches appended; no exact Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-injective-target-hom-symbol.json`: one new statement-only lemma, unsplit, no exact Mathlib match after LeanFinder (two phrasings), Loogle, LeanSearch and two Mathlib grep searches.
- `citations.json`: one verbatim statement quotation for each of the item's 17 step/node citations.
- `report.md`: this report. `searches.jsonl` is the search command's original log, not a reconstructed record.

## Attachments

None. I searched the read-only slopmaster2 WeilConjectures and Comparator trees for the exact blueprint tag and the filtered Hom notion. The tag has no declaration; the broad matches are about filtered index categories or filtered colimits, not the present shift filtration. The ordinary HomComplex APIs of Mathlib do not attach this full filtered statement. The master checkout is not used as evidence of a finished proof.

## WANTED

None. The sources needed for this split are present. I do not invoke the Illusie reference cited by Varshavsky as an additional black box.

## What was wrong or missing

The item was a correct statement-only child of the reviewed filtered-derived-Hom split. It needed a proof rather than a change of hypotheses. Its graded Hom decomposition cannot be justified simply by saying that the target filtration splits: the source filtration need not split, and arbitrary symbols must be extended to maps defined on the entire source. This extension problem is isolated as the new symbol-sequence node. It is a statement about two filtered objects, without complexes, differentials, homotopies, quasi-isomorphisms, or localization, so it neither restates an item clause nor moves the whole invariance assertion into a child.

A second distinction is important: the existing filtered-localization injective-model node assumes that the category has enough injectives. This item does not. I use the already supplied injective graded terms, not the existence of injective resolutions. The two ordinary K-injective Mathlib leaves used in Step 8 apply to an arbitrary abelian category; enough injectives is not introduced.

The proof is marked agent-origin: Varshavsky §5.1.5 motivates the concrete model, but does not print these signed calculations. Stacks 05TP supplies the finite splitting input for the smaller symbol lemma, and 070J/070I supply the ordinary K-injective comparison. No SGA source is used. The inherited blueprint ancestry and the sk-i-curve-zero unit route remain unchanged. The current main-20261015 locality node and the unit both place this under localization trace additivity in the contracting-correspondence argument; no unit or chapter file is edited.

## What could not be finished

Nothing in the assigned one-level split remains open. The new node is intentionally delivered with only its statement and recorded searches, for its own later split. No Lean file was written, no compiler or Lake command was run, and the shared project and launcher were not modified.

## Review by Q45

I read the worker brief, the stage-1 contract, the three blueprint levels in SETUP.md, delivery-errors B–E in full, GOAL.md and dag-sync.md. I read the chapter and unit records, the current main-20261015 text for lem-trf-local-term-locality, and the parent lem-trf-filtered-derived-hom-calculus statement and proof. The item is a concrete model lemma below that parent, not the unit's key statement, so the unit's realized fields need no change.

For the mathematics I read Varshavsky pp. 40–41, especially Lemma 5.1.4 and §5.1.5. I read Stacks derived.tex `lemma-filtered-injective` (05TP), `lemma-morphisms-into-filtered-injective-complex` (05TY), `lemma-K-injective` (070I), and `lemma-bounded-below-injectives-K-injective` (070J). I also read homology.tex `definition-injective` (0135). I distinguished the actual claims of these sources: 05TY does not itself print a chain-level graded Hom comparison, and 05TP gives a splitting of objects, not a chain-compatible splitting. The proof does not assert either stronger claim. I read Mathlib HomComplex.lean δ_comp and δ_ofHomotopy and the KInjective.lean statements at HomotopyCategory lines 42–43, 133–135 and DerivedCategory lines 41–46. The ordinary Hom calculations are useful candidates, but they do not supply the finite shift-filtration assertion in one specialization.

Step 1 uses exactly the Hom abelian groups, additive composition, zero objects and complex differential identities of def-sp-abelian and def-weil-abstract-derived-category. Expanding the two mixed terms proves d²=0; the explicit lower bound i₀−p₁ verifies that the direct-sum Hom model is bounded below. Bounded P makes all Hom families finite, so no infinite product or coproduct in the original category is assumed.

Step 2 uses the decreasing filtration definition and the actual subcomplex/quotient-complex definition in def-sp-filtration and def-sp-filtered-complex-subquotients. I checked the endpoint inequalities r≤c−b and r≥d+1−a with decreasing, not increasing, filtrations. The proof checks both the differential and uniformity in cochain degree. Step 3 uses the same filtration definition and the chain-map equation in def-weil-abstract-derived-category, together with additive composition from def-sp-abelian. Its component formulas prove all functoriality clauses and commutation between the two variables.

Steps 4 and 5 cite def-sp-abelian and def-sp-filtration only for composition, addition and preservation of subobjects. Their arguments are explicit substitutions in the already defined differential: source homotopy S(f)=(-1)^n f h cancels the two d_I f h terms, whereas target homotopy T(f)=k f cancels the two k f d_P terms. Both homotopies preserve every shift filtration step. Applying those formulas to the given inverse-homotopies proves the homotopy-equivalence clause. No homotopy comparison theorem is silently cited.

Step 6 takes the exact quotient-isomorphism and naturality from the new symbol-sequence statement. I checked that it allows arbitrary finitely filtered source objects and needs injectivity only of the target grades, exactly as supplied by the item's last paragraph. def-sp-filtered-complex-subquotients defines the quotient differential; the displayed (p,i) component calculation verifies that the degreewise symbol isomorphism commutes with it. The new lemma has no chain-complex comparison hidden in its statement, and the item proves that compatibility itself. The finite reindexing uses boundedness of P and the fixed filtration interval.

Step 7 is elementary: cocycles are precisely maps to B[n] and coboundaries are precisely homotopies after multiplying the degree-minus-one family by (-1)^n. I checked the sign against d_{B[n]}=(-1)^n d_B in the cited derived-category definition; the formula gives naturality under precomposition directly. It does not assume injectivity.

Step 8 applies lem-weil-pbc-bounded-below-injectives-kinjective to each shifted graded target. Its statement explicitly allows an arbitrary abelian category. The terms of the shifted grade are injective by hypothesis, and the bounded-below bound is shifted but still finite. I then use exactly the Hom_K-to-Hom_D bijection stated by lem-weil-pbc-kinjective-hom-derived. Naturality is the functoriality of localization on the same representative chain maps; precomposition by an invertible derived morphism has its displayed inverse. Thus the argument proves every cohomology degree, not merely H⁰. Finally, coordinatewise kernels and images show that the finite sum retains these bijections. Both cited results are existing Mathlib leaves; no off-unit non-leaf theorem is used as a route replacement.

For the new node I checked self-containment, quantification of all four filtration endpoints, the extension-property meaning of injective, the finite range of the sum, and both naturality directions. Here is the argument supporting its correctness, recorded only in this report because the new node must remain statement-only. Split Y as a finite sum of its injective grades using the existing lem-trf-injective-graded-filtration-splits (Stacks 05TP), choosing the graded identifications to be the identity by composing each summand's identification. Given a proposed symbol φ_p:gr^p X→gr^{p+r}Y, extend it along the monomorphism F^pX/F^{p+1}X→X/F^{p+1}X to the injective summand J_{p+r}. Compose with X→X/F^{p+1}X, and combine the finitely many target components. The q-component, where q=p+r, vanishes on F^{p+1}X and therefore on every F^kX with k>p. Consequently the combined map sends F^kX into the tail sum with q≥k+r, which is F^{k+r}Y, and has the prescribed symbols. A symbol is zero exactly when each f(F^pX) lands in F^{p+r+1}Y, namely when f lies in G^{r+1}. Taking induced quotient maps proves naturality; the auxiliary splitting disappears from the canonical symbol map. This simultaneous extension and kernel comparison is the non-elementary fact isolated by the new node. It is not merely the injective definition, not the splitting theorem, and not a clause of the invariance item.

I tested zero source, zero target, a single filtration grade, zero intermediate grades, negative endpoints, and r outside the support. For pure grades p and q the only nonzero symbol degree is r=q−p, which checks the sign of the shift. The target-injectivity hypothesis is essential: take X=Z/4 with F⁰X=X, F¹X=2X, F²X=0, and Y=Z/2 pure in filtration degree 1. At r=0, every X→Y kills 2X, so the prescribed nonzero gr¹X→gr¹Y symbol cannot lift. This is excluded by the new lemma because Y is not injective. No project statement needed correction or a STATEMENT-DISPUTED marker.

Before creating the node I searched all dag/nodes by filtered Hom, symbol, graded/injective Hom, and 05TP, ran blueprint_refs search for “Hom complex”, “filtered Hom”, “symbol” and “graded morphisms”, and searched slopmaster2 by the same notions. I read the statements of the nearby filtered-operation, filtered-injective-model, filtered-bifunctor-graded-comparison, and hom-dual-homotopy nodes. The natural derived graded comparison assumes a filtered lift already exists and cannot provide this concrete pre-localization symbol sequence without circularity. All six new-node searches were actually run through msearch.py and retained with their exact query text and result log; none was unavailable. Fresh item searches supplement the inherited records, including the inherited LeanSearch outage honestly retained as unavailable. Every proof step is shorter than 2000 characters (maximum 1158), and the only non-elementary graded comparison has been extracted, not hidden in a long step. I prepared the exact per-step citation quotations from the statements themselves, rather than from their proofs.

## Not duplicates

lem-trf-injective-target-hom-symbol vs lem-trf-injective-graded-filtration-splits: the latter identifies a single filtered injective object with a sum of its grades; the new node proves surjectivity, kernel and naturality of symbols of morphisms from an arbitrary, possibly nonsplit, filtered source.

lem-trf-injective-target-hom-symbol vs def-trf-finite-filtered-localization: that node defines the localized categories and concrete complex functors; it states no exact symbol sequence for object Hom groups.

lem-trf-injective-target-hom-symbol vs lem-trf-enough-strict-filtered-injectives: the existing extension theorem concerns a strict monomorphism and a filtration-preserving map already defined on it, not lifting an arbitrary tuple of grade symbols from X to Y; the new statement constructs the Hom quotient and identifies its kernel and naturality.

lem-trf-injective-target-hom-symbol vs lem-trf-filtered-localization-injective-model: the existing theorem is about injective replacements, localization Hom bijections and an equivalence of homotopy categories, with enough injectives; it does not state the object-level symbol sequence.

lem-trf-injective-target-hom-symbol vs lem-trf-filtered-derived-operation-lifts: the existing theorem concerns derived sheaf operations and their filtered lifts, not the concrete shift-filtered Hom quotient of two objects in an arbitrary abelian category.

lem-trf-injective-target-hom-symbol vs lem-trf-filtered-derived-hom-calculus: the existing theorem constructs derived filtered Hom and its derived graded formula. The new node is a pre-localization object calculation used in the proof below that theorem; citing the derived construction instead would be circular.

lem-trf-injective-target-hom-symbol vs lem-trf-filtered-bifunctor-graded-comparison: the latter assumes an exact filtered lift on derived categories exists, whereas the new node identifies an explicit quotient of groups of ordinary object morphisms without any lift assumption.

lem-trf-injective-target-hom-symbol vs lem-trf-hom-dual-preserves-homotopies: the latter is an unfiltered homotopy calculation for complexes of modules; it has no Hom symbol sequence and no injectively graded filtered-object assertion.
