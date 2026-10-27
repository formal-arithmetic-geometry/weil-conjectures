# Q159 stage-1 delivery: lem-trf-parameter-product-reduced-cartier

## Files written

- dag/nodes/sec-trace-formula/lem-trf-parameter-product-reduced-cartier.json: statement node, now split into four proof steps. No complete Mathlib match; no statement or statement-dependency change.
- citations.json: nine exact statement extracts for the nine step/node citations.
- report.md: this report. searches.jsonl contains the five actual searches made in this sandbox. ilo.txt is a sandbox-only text extraction of the source PDF.

There are zero new nodes and zero new Mathlib leaves. The proof reuses existing DAG statements rather than creating specializations of them.

## Attachments

None. The exact blueprint-tag search and searches for regular systems of parameters, parameter products, radical ideals and Cartier divisors in lean/WeilConjectures found no declaration stating this entire item. Nearby regular-local and regular-immersion declarations cover different assertions. No Lean was written or compiled.

## WANTED

None. I read the local ILO PDF and the local Stacks sources cited below.

## Findings and changes

The imported statement is correct, including empty products and empty schemes, so no STATEMENT-DISPUTED correction was needed. Its proof was empty. The existing lem-sfb-transverse-prime-ideal-parameters, clause (b), already gives the exact local parameter-product intersection, nonzerodivisor and radicality assertions. I used that stronger existing theorem rather than making another parameter-product algebra node. Regular-local domains, quotient localization, stalkwise Cartier spreading and density also already have nodes.

I read the chapter and unit records and preserved the existing ancestry from lem-trf-local-term-locality through nearby-duality and log-regular boundary desingularization. This is the ordinary-local algebra needed by that existing route; no alteration or six-functor route is replaced. ILO VI 1.4 gives density of the trivial-log locus, VI 1.7 the normal-crossings boundary on a regular log-regular scheme, and VIII 4.1.1--4.1.2 the parameter-product equations. These paragraphs do not themselves prove all the ordinary-local algebra in this auxiliary item. Therefore proof_origin.by is agent, with the actual Stacks-backed assembly written out and its sources specified per step.

## Unfinished work

None for this one-level stage-1 split. Existing unsplit dependency nodes retain their own future work; this delivery does not claim to prove their statements in Lean or split them again.

## Review by Q159

I read ILO Expose VI 1.4 and 1.7, printed pp. 69--70, and VIII 4.1.1--4.1.2, printed p. 117, in the local PDF text. I also read Stacks algebra.tex Tags 00NP (lemma-regular-domain), 00NQ (lemma-regular-ring-CM) and 00CT (proposition-localize-quotient), morphisms.tex Tag 01QO (lemma-closed-immersion), schemes.tex Tags 01J0--01J1 (definition-reduced and lemma-reduced), and divisors.tex Tags 0AG8 (lemma-effective-Cartier-in-points) and 07ZU (lemma-complement-effective-Cartier-divisor). No new node needs an additional source review.

For step 1 I opened def-weil-regular-scheme, lem-sc-regular-local-domain, and lem-sfb-transverse-prime-ideal-parameters. The definition provides regular local stalks; the domain theorem states nonzeroness as well as absence of zero divisors. Clause (b) of the transverse-parameter node expressly states all the product, prime-ideal incomparability, radicality and nonzerodivisor facts used here, including r=0. The item's hypothesis gives selected positions of ONE regular system, so permuting that system really puts the selected nonunit germs first; there is no assumption that independently chosen systems are compatible. The unit factors yield f_y=uT, so equality of principal ideals and preservation of injective multiplication follow by multiplication by the inverse unit. Prime elements follow from nonzero generators of the cited prime principal ideals; nondivisibility follows from incomparability. I did not invoke the UFD factorization theorem or its proof.

For step 2 I opened def-weil-closed-immersion, the Mathlib leaf lem-weil-pbc-localization-at-prime-of-quotient, and def-pc-reduced-scheme. The affine closed-immersion description applies to the GIVEN closed subscheme V(f), whose affine ideal is (f|_U). The quotient-localization leaf has no Noetherian or regularity restriction and gives exactly B/(f_y) for the local ring at a point of H. Its formula on fractions checks which ideal is transported. The radical-quotient implication is written out using an arbitrary nilpotent class, and the reduced-scheme node defines reducedness by these local rings. No conclusion about the stalks is borrowed from a node that only defines an ideal-sheaf kernel.

For step 3 I read the entire statement of lem-sfb-stalk-nonzerodivisor-cartier-spreading, including its scheme clause, and def-nagata-effective-cartier-ideal. The spreading theorem assumes locally Noetherian X and a closed subscheme, both supplied here, and requires a nonzerodivisor generator at every stalk, supplied in step 1. It explicitly permits the unit ideal outside H and the empty divisor. Its conclusion is the effective Cartier ideal in the cited definition. This step does not confuse a stalk generator with a neighborhood generator without an intervening theorem.

For step 4 I opened lem-pc-cartier-divisor-nowhere-dense. Its statement applies to an effective Cartier ideal on an arbitrary scheme, and explicitly concludes topological density. Thus the step uses neither a hidden irreducibility assumption nor a global Noetherian assumption. The identification with D(f) is just the affine vanishing-set definition, compatible on overlaps.

I tested a field (all germs necessarily units), r=0, Y empty, and H empty. I also tested the usual node xy=0 inside Spec k[x,y]: at the origin its germ ideal is (x) intersect (y), whereas away from one axis the corresponding other factor is a unit; the proof uses the correct varying J_y. Repeated parameters such as x*x are excluded by distinct positions, as required since (x^2) would not be radical. Arbitrary nonunits not in a parameter system are not silently allowed. No nonempty scheme point has the zero ring as its local ring.

I checked delivery-errors B--E individually: no new statement-only nodes, no duplicate specializations, no invented search records, no misuse of a definition as a theorem, no source-only non-elementary citation, no undeclared proof dependency, no relabelling into a new node, no step over 2000 characters, and all cited statements were opened. The four nontrivial off-unit results are declared in split_report.tool_uses with their precise generic purpose. The quotient-localization result is already a Mathlib leaf. citations.json contains an exact substring of each cited statement, checked directly against the current node files.

The Mathlib searches returned basic-open and reduced-stalk results, squarefree-product results, radical_mul and primary-decomposition results. None states the complete regular-parameter scheme assertion or specializes to it in one line. I tried the scheme formulation and a second regular-local-ring formulation, and preserved the earlier item's search records as well as recording all five new actual queries. I used no direct Mathlib search outside the required msearch.py command; reading the returned squarefree source confirms the missing parameter and Cartier assertions.

## Repair of the returned delivery

The returned retained head was bcb9e20fd8f. The landing refusal named one changed dependency: lem-sfb-stalk-nonzerodivisor-cartier-spreading. I compared the retained item with the current live item (still unsplit): its statement, statement dependencies, source and blueprint provenance agree. I retained all four proof steps, the earlier report, citations and logged Mathlib searches; the search question and statement have not changed, so I did not repeat those searches. The delivery tool rebuilds the repaired delivery on the current server DAG.

I opened every current statement in the item's statement and proof dependencies. Eight of the nine retained step/node quotes still match verbatim. The sole failed quote was the scheme clause of lem-sfb-stalk-nonzerodivisor-cartier-spreading: its reviewed wording now explicitly identifies the module stalk of the closed-subscheme ideal sheaf, with references to def-weil-pbc-module-stalk and def-sbc-closed-immersion-ideal-sheaf. This introduces no extra mathematical hypothesis. Its current scheme clause still assumes a locally Noetherian scheme and a closed subscheme, and concludes that the ideal sheaf is effective Cartier if its ideal stalk at every point has a nonzerodivisor generator.

I rewrote step 3 to name that same ideal sheaf I, its inclusion into O_Y, and the stalk ideal I_y=(f_y). The generator is obtained from the given affine principal equation, and step 1 supplies injective multiplication at every point, including the unit generator off H. Thus this is precisely the object and the hypothesis in the changed criterion; no assertion is taken from its proof. I replaced the stale sentence in citations.json with the complete current hypothesis/conclusion sentence verbatim. I reread Stacks 0AG8 (divisors.tex, lemma-effective-Cartier-in-points, lines 2939--2972); its condition at points of H suffices, and the stronger everywhere condition used here holds because off H the ideal is (1). The criterion still explicitly includes the empty closed subscheme.

For the other steps, the current regular-local domain and transverse-parameter clause (b) still give every local prime/intersection/radical/nonzerodivisor assertion in step 1, including the empty product. The current closed-immersion, quotient-localization and reduced-scheme statements still give the local-ring computation and reducedness in step 2. The current Cartier-complement statement still gives topological density in step 4 without an irreducibility assumption. I checked these hypotheses again on fields, the empty scheme, r=0 and the two distinct coordinate parameters; a repeated coordinate would fail the stated distinct-position hypothesis. All four steps remain shorter than 2000 characters. No new nodes or leaves were introduced, and the original statement and its dependencies are preserved. This repairs the single landing-refusal point in the node, citation file and report, rather than just rebasing the rejected content.
