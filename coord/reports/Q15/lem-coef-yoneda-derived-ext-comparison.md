# Worker report

1. Files written: `dag/nodes/sec-six-functors/lem-coef-yoneda-derived-ext-comparison.json` (statement, now split, no whole-item Mathlib match); `citations.json` (verbatim backing for every proof-step citation). No new nodes or Mathlib leaves. All mathematical arguments belong to the item's eleven proof steps.
2. Attachments: none. Searched the read-only slopmaster2 `WeilConjectures/` for the exact blueprint id, Yoneda/Ext combinations and notions; the hits concern ordinary categorical Yoneda, not exact-sequence Yoneda extension classification. No project declaration proves this item.
3. WANTED: none. The required Stacks sources are present locally.
4. Source and imported-material issues: the item statement is correct and unchanged. Stacks 06XU omits the maps out of the common extension and writes the common-refinement endpoint equations as equalities without distinguishing chain maps from homotopy classes. Step 5 supplies the explicit homotopy correction; step 6 supplies the quotient-induced morphisms. These fill details, without changing the route or the statement. The existing fraction nodes have correct tags but inaccurate textual labels: 04VI is `lemma-morphisms-right-localization`, not `categories-lemma-right-localization-finite-diagram`; 04VJ is `lemma-equality-morphisms-right-localization`, not `categories-lemma-right-localization-equal-morphisms`. Their statements are usable and their mathematical content is correct. I did not edit these other nodes.
5. Nothing mathematical remains unfinished. Delivery is reserved for the second reader after a successful dry run.

## Searches and reuse

The sandbox `searches.jsonl` contains the five searches actually run with the required `msearch.py`: two different LeanFinder phrasings, Loogle `"Ext", "ShortExact"`, a grep for `yoneda|extClass` in `Algebra/Homology/DerivedCategory/Ext`, and LeanSearch for Yoneda n extensions and Baer sum. Every service answered. The item's `mathlib_searches` records these exact queries and the returned names. I read `Ext/Basic.lean` (the definition and universe discussion, lines 14–105) and `Ext/ExtClass.lean` (lines 39–105). Derived Ext, its equality criterion, and the class of a short exact sequence do not classify actual higher exact sequences modulo endpoint-preserving zigzags. Thus this is not a whole-item Mathlib leaf.

Searched the whole DAG by Yoneda extension, Baer, fraction, and exact pushout notions, and the Stacks tags. Ran `tools/blueprint_refs.py search` for Yoneda, Baer, fractions and truncation, and `ancestor` for this item. The general Yoneda lemma is unrelated; the sheaf-specific Ext naturality nodes do not supply the general comparison. The disk/sphere extension node concerns Ext in the category of complexes, not this comparison. Reused the existing generic multiplicative-system, right-fraction representation/common-refinement, and short-exact pushout nodes. No duplicate or clause-restating node was created. The existing `blueprint.from` already names the coefficient-adjunction paragraph precisely and remains valid; `same_as` is empty after search. I read the current main-20261015 exceptional-adjoint source and the inherited chapter/unit records. This is an auxiliary abelian-category tool in its inherited coefficient branch, not a replacement for a geometric or coefficient-transport proof. No SGA source is used.

## Review by Q15

I read `derived.tex` at the Yoneda-extension definition, roof construction, Lemma 06XU, and Lemma 06XV (around lines 8773–8897). I also read `homology.tex` at Example 05PJ, Lemmas 08N3/08N4, and Section 010I from the definition of extensions through the pullback/pushout and Baer constructions (around lines 700–719, 852–915 and 1260–1417). For the localization facts I read `derived.tex` Lemma 05RT and `categories.tex` Definition 0BM3 and Lemmas 04VI/04VJ (lines 4600–4660), checking the actual tag mapping. The proof keeps the roof-and-pushout argument of 06XU and fills its omitted verifications rather than citing the classification as its own auxiliary lemma.

I opened all eight cited nodes and read their statements. In particular the fraction nodes state representation and equality by a common right refinement, the multiplicative-system node supplies the needed hypothesis specifically in the homotopy category, and the short-exact pushout node supplies the full exact sequence after arbitrary change of its left endpoint. The injective definition states extension of morphisms across any monomorphism; it is not used as an existence theorem for resolutions.

Step 1 uses `def-pc-ext` and `def-weil-abstract-derived-category` for shifted Hom, localization, cohomology and additivity. Exactness directly computes the augmentation's cohomology; the equations for an extension morphism show invariance without invoking classification.

Step 2 uses both the multiplicative-system and fraction-representation statements, with source category K(A), not the category of chain maps before quotient by homotopy. Its truncation is written explicitly and checked by the kernel/image cohomology formula of the derived-category definition, so it does not take a truncation theorem from an unrelated definition node.

Step 3 uses the abelian-category definition and the actual short-exact pushout theorem. Vanishing H^(-i)(L) allows f to descend to im d. The pushout theorem applies to the monomorphism im d into L^(-i+1), with arbitrary endpoint map to V. Its conclusion is exactly the initial short exact sequence needed. Splicing the remaining terms uses the already established negative-cohomology vanishing. The quotient uses (d,-f), with this sign checked against the class-comparison chain map in step 4. In degree one P already is the final middle object: no extra L^0 is inserted.

Step 4 writes every component of the chain map L to C_E and the only new differential equation. It uses the derived-category definition to invert quasi-isomorphisms; surjectivity follows from the written equations, not a new classification node.

Step 5 uses the common-refinement statement with its hypotheses supplied by the multiplicative-system statement. Equality is initially in K(A). After upper truncation any homotopy into U[0] is zero because L^1=0. The other homotopy has component h:L^(-i+1) to V; adding dk+kd to b, with k landing in the initial V of C_E', changes precisely its numerator and leaves the augmentation unchanged. This is the substantive correction to the omitted source details, and also works at i=1.

Step 6 uses only the abelian cokernel universal property after step 3. The formula (a^(-i+1),j_E) kills (d,-f), so it really descends to P. Its later components are a, and its endpoint components are identities. Repeating with corrected b supplies the common extension, including both commuting endpoint squares; there is no appeal to unquoted constructions in another node's proof.

Step 7 uses the pushout theorem for arbitrary endpoint maps and again in A opposite for pullback. The opposite is abelian directly by reversing the kernel/cokernel axioms in `def-sp-abelian`. Thus no additional monicity of v, epicity of u, or enough-injectives hypothesis is smuggled in. Direct-sum exactness is the finite block-diagonal kernel/image calculation, written as a step rather than a new node.

Step 8 uses the two natural chain maps to compute the class formulas through the augmentations, with Ext's variance exactly as `def-pc-ext` states. Step 9 applies those formulas to the diagonal and sum, and uses the biproduct definition of addition. Associativity, identity, commutativity and inverses then follow by the proved bijection with an abelian group, so no uncited Baer-group-law theorem is assumed. The zero representative is explicit in every positive degree.

Step 10 uses the written retraction null-homotopy and then the already proved classification. Its kernel/cokernel argument shows that every degree-one endpoint-preserving arrow is invertible, so a zigzag to the split sequence really implies splitting. Step 11 takes the retraction from the injective-object definition and checks the sole nonzero homotopy component; surjectivity already proved then gives all higher injective vanishings.

I checked the small cases i=1, i=2, U=0 and V=0; a split short exact sequence; and an arbitrary injective V in a category that need not have enough injectives. For i=2 the zero extension has E_1=V, E_0=U and middle map zero, so its exactness and contracting component are valid. For i=1 the zero model uses V direct-sum U and projection onto V, not the identity on its entire middle term. This last clarification was corrected during self-review. All size conventions are inherited from the given derived Ext; there is no small-index colimit or resolution existence assumption. No new statement needs separate edge-case testing. B1–B10 create no new-node obligations here; C1–C8 were checked against each actual cited statement and the off-unit generic pushout tool is declared in `split_report.tool_uses`; D1–D5 are met by the explicit roof, quotient and homotopy arguments; E1–E6 were checked as above. There is no statement dispute or change to maintainer-owned unit metadata.

## Not duplicates

No new nodes.

## Validation

The required validation command is `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q15 lem-coef-yoneda-derived-ext-comparison --no-push`. It runs the delivery and DAG preflight checks. The worker reports READY only after this command prints OK. No compiler, Lake or build command has been run.

## Second reading by Q15

I reread the item statement against Stacks `derived.tex`, Tag 06XU (`lemma-yoneda-extension`), Tag 06XV (`lemma-ext-1`), and `homology.tex`, Tag 010I (`section-extensions`), including the exact endpoint and Baer-sum constructions; verdict: all hypotheses and clauses agree with the intended source route.

Step 1 was checked against the definitions of derived Ext and the derived category in `def-pc-ext` and `def-weil-abstract-derived-category`, and against the 06XU class construction; verdict: the augmentation, projection chain map, and invariance argument are valid.

Step 2 was checked against 06XU's right-fraction and upper-truncation argument and the statements of `lem-pc-quasi-isomorphisms-multiplicative-system` and `lem-pc-right-fraction-representation`; verdict: the truncation retains the required cohomology and no positive-degree hypothesis is added.

Step 3 was checked against 06XU's quotient construction, Homology 05PJ/08N4, and `lem-weil-pbc-pushout-short-exact-sequence`; verdict: the image factorization, pushout relation, splice, and the separate $i=1$ endpoint case are correct.

Step 4 was checked componentwise against the complex definition and the cokernel presentation of the pushout; verdict: the displayed relation gives the chain map and the quasi-isomorphism follows by the two augmentation quasi-isomorphisms.

Step 5 was checked against `lem-pc-right-fraction-common-refinement` in the homotopy category and the explicit degree $-1$ correction; verdict: upper truncation makes the augmentation equality strict and the sign of the correction gives strict equality of the numerator maps.

Step 6 was checked against the cokernel universal property and the endpoint diagrams in 06XU; verdict: both induced maps of extensions are defined, fix $V,U$, and establish equivalence.

Step 7 was checked against Homology 010I, 05PJ, 08N3, and 08N4, including the opposite-category pullback argument; verdict: pushout, pullback, and finite direct-sum exactness use only the stated abelian hypotheses.

Step 8 was checked against the functoriality clauses of `def-pc-ext` and the chain maps for pullback, pushout, and direct sum; verdict: both variance formulas and naturality are correctly typed.

Step 9 was checked against the Baer construction in Homology 010I and the additive structure in `def-pc-ext`; verdict: diagonal/pushout addition, negation, and the explicit split zero representatives work in every positive degree.

Step 10 was checked against 06XV and the kernel/cokernel argument in `def-sp-abelian`; verdict: degree-one zero class is exactly split, since every endpoint-fixing morphism is an isomorphism.

Step 11 was checked against the injective extension property in `def-sp-injective-resolutions`; verdict: the retraction supplies the stated null-homotopy in every positive degree, with no enough-injectives assumption.

There are no new auxiliary nodes or Mathlib leaves to inspect; the eight reused nodes were checked for exact statement support and their verbatim statements are recorded in `citations.json`. I also checked $i=1$, $i=2$, $U=0$, $V=0$, split extensions, and injective $V$; all edge cases agree with the construction. No mathematical or source correction was needed. The only second-reading addition is this per-step audit and explicit edge-case record. The dry run passed with `OK (not pushed)`.
