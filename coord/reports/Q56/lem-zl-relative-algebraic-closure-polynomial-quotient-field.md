# Stage-1 report: lem-zl-relative-algebraic-closure-polynomial-quotient-field

## Files written

- dag/nodes/sec-deligne-laumon-general/lem-zl-relative-algebraic-closure-polynomial-quotient-field.json: statement, split; unchanged statement and statement dependencies; no full Mathlib match.
- citations.json: one verbatim statement quotation for each node used by each proof step.
- searches.jsonl: six actual msearch.py searches, retained with their output digests; the item also retains its inherited searches.
- report.md: this report.

No new nodes and no new Mathlib leaves. All three non-elementary algebra inputs already have nodes.

## Attachments

None. Searched lean/WeilConjectures for the item's blueprint tag and for relative algebraic closure, subfields, coefficient integrality, polynomial quotients and PID terminology. No project declaration was found stating this complete item. Nearby field/scheme declarations and quotient-field usages do not give coefficient descent under this hypothesis. No compiler or Lake command was run.

## WANTED

None.

## Findings and changes

The item was an unsplit extraction from the reviewed split of lem-zl-field-extension-algebraically-closed-geometric; the sandbox contained no prior node, report or searches. There is no released repair note for this item. Its statement is correct as written, including the absence of a separability hypothesis. I preserved the statement, its statement dependencies, all existing metadata and the inherited Mathlib searches. The proof now normalizes any factorization, descends both monic factors coefficient by coefficient, invokes irreducibility over k, proves maximality of the polynomial ideal using principality, and concludes with the field's one-point spectrum.

The reusable coefficient theorem is lem-zl-monic-divisor-algebraic-coefficients, already a Mathlib leaf. The integer/rational-only lem-weil-monic-divisor-integral is insufficient here. The polynomial-PID node lem-pur-polynomial-field-pid and the quotient-by-maximal-ideal node lem-weil-common-extension-fields-quotient-field are existing Mathlib leaves. The spectrum definition explicitly includes the one-point spectrum of a field, so no additional node is needed. These leaves are generic algebra tools; their use changes no unit or chapter route.

Mathlib searches used leanfinder twice with different phrasings, loogle, leansearch, and two grep patterns through the required msearch.py command. All six returned successfully. I read the hits and the relevant pinned source: Polynomial.isIntegral_coeff_of_dvd at IsIntegral.lean:62-73 gives the existing coefficient leaf; integralClosure.mem_lifts_of_monic_of_dvd_map at GaussLemma.lean:55 onward gives lifts to integral closure. The irreducibility Gauss lemma at GaussLemma.lean:149 assumes a fraction field; Polynomial.Separable.map_irreducible_of_isPurelyInseparable at Tower.lean:284 assumes a separable polynomial and a purely inseparable extension. They do not state this item for an arbitrary relatively algebraically closed extension. Polynomial.Monic.irreducible_of_irreducible_map has the opposite direction. No exact match or one-line specialization proving the complete item was found.

The main-20261015 blueprint ancestor file lem-zl-bertini-finite-cover-curve.md currently contains its statement without a proof. I read it and the chapter and unit records. The inherited from.place/via describes the geometric irreducibility input beneath that Bertini result, through Tag 0G33 and Tag 037P. This split realizes the precise monic-factor/quotient-field part of that existing route, without changing either level above it. Searches of the whole DAG and blueprint for monic, monic divisor, relative algebraic closure, irreducible polynomial, quotient field, spectrum of a field and Bezout found no blueprint restatement to attach.

## Not duplicates

There are no new nodes. The split reuses lem-zl-monic-divisor-algebraic-coefficients rather than duplicating it; reuses lem-pur-polynomial-field-pid and lem-weil-common-extension-fields-quotient-field rather than creating their specializations; and uses def-weil-affine-spectrum for its explicit field clause. It does not cite its parent or any node depending on this item.

## Review by Q56

I read Stacks algebra.tex, Tag 037P (lemma-field-extension-geometrically-irreducible), including its full proof, and Tag 00H6 (lemma-polynomials-divide), including the coefficient-integrality statement and proof. This is the source's factor-descent argument. For the quotient justification I read Tag 030A (lemma-polynomial-domain-normal), whose proof explicitly says K[x] is Euclidean and hence a PID, and Tag 00BS (item-characterize-maximal-ideal), which states the field-quotient characterization. I also read the pinned Mathlib implementations of the cited coefficient theorem, Polynomial.instEuclideanDomain at FieldDivision.lean:357 and Ideal.Quotient.field at Quotient/Basic.lean:145. There are no new nodes needing separate sources.

Step 1 cites the field-extension node for injectivity, the polynomial-ring node for its exact coefficient convolution and definitions of degree/leading coefficient, and the coefficient-map node for the map's coefficients and multiplicativity. I checked these node statements themselves. Computing the coefficient of the sum of the two degrees proves leading-coefficient multiplication over a field; it also proves units are nonzero constants. This explicitly rules out P=0 and constant P, shows its image stays monic and nonunit, and justifies the scalar normalization Q=a^{-1}A, R=aB with ab=1. This is an elementary computation, not an uncited factorization theorem.

Step 2 uses the exact statement of lem-zl-monic-divisor-algebraic-coefficients twice: both P and the chosen divisor must be monic, and both Q and R divide P_K. Step 1 verifies all those hypotheses. The relative algebraic closure assumption is the item's own hypothesis; it turns the lemma's algebraic coefficients into coefficients in the image of k. The field-extension and coefficient-map statements give injectivity and multiplicativity; uniqueness of coefficient lifts preserves zero outside the finite support, hence defines actual finite polynomials. Injectivity descends the product identity. I did not take any stronger factor-descent assertion from the coefficient lemma.

Step 3 uses irreducibility of P exactly as the statement defines it. The only cited node is the coefficient map, whose ring-homomorphism clause is enough: mapping an explicit inverse gives an inverse. Undoing multiplication by the nonzero scalar gives a unit factor in the original arbitrary factorization. No separability or splitting-field theorem is used.

Step 4 takes only principality and the domain assertion from lem-pur-polynomial-field-pid, applied to the field K; its statement explicitly quantifies over every ideal of K[T]. I wrote out the maximality argument rather than quoting an uncited irreducible-ideal lemma: for (F) contained in J=(G), F=GH, and irreducibility makes either G a unit (J is the whole ring) or H a unit (J=(F)). The ideal is proper because F is not a unit. This verifies the maximal-ideal hypothesis of lem-weil-common-extension-fields-quotient-field before applying its exact statement. The quotient is nonzero because it is a field. This step does not require finite-dimensionality or finite generation.

Step 5 takes the one-point spectrum clause verbatim from def-weil-affine-spectrum, whose statement I read, then directly verifies the closed-cover definition of irreducibility in def-weil-irreducible-components. The references in citations.json quote precisely these node statements; a citation never stands in for a different theorem hidden in its proof.

I checked small cases: K=k and linear P produce a quotient isomorphic to K. Over k=F_p(s), K=k(t), the inseparable polynomial P=T^p-s remains covered: algebraicity of coefficients and descent require no distinct roots. Over R contained in R(t), P=T^2+1 likewise fits. Dropping the relative-closure hypothesis fails for Q contained in Q(i) with T^2+1, confirming that the proof uses the necessary hypothesis. No P=1 or P=0 can satisfy the item's irreducibility assumption, and zero factors cannot occur in a factorization of the monic nonzero image.

Against delivery-errors B-E: all objects and hypotheses are introduced in the unchanged self-contained statement; notation remains single-escaped TeX; the sources have checked Stacks tags and labels; no new unsplit node carries a concealed proof; no elementary, duplicate or clause-only node was created. Every non-elementary external fact is a cited existing statement that supplies precisely what is used. The remaining steps are displayed coefficient, scalar, ideal or singleton computations. No proof step exceeds 2000 characters (lengths 710, 668, 406, 524, 370). No source error, statement dispute, cycle or off-unit non-Mathlib tool is introduced. No SGA source was used.

## Unfinished work

None in the requested one-level split. Delivery validation and push results are reported by the delivery tool.

## Dry-run repair

The first dry run rejected the phrase “the item’s hypothesis” in step 2 as a standalone-statement wording issue (B2). Replaced it by the explicit hypothesis on elements of K algebraic over k. No statement, mathematical step or citation changed.
