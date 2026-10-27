# Q72 stage-1 delivery

Item: lem-sfb-normal-domain-monic-prime-factorization. Date: 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-normal-domain-monic-prime-factorization.json: item, split in four steps; statement and existing provenance/search records retained.
- dag/nodes/sec-six-functors-basics/lem-sfb-normal-monic-divisor-descent.json: statement; Mathlib leaf, IsIntegrallyClosed.eq_map_mul_C_of_dvd, Mathlib/RingTheory/Polynomial/GaussLemma.lean:80-83, specialized to a monic divisor.
- citations.json: every step/node pair, with a verbatim statement quotation.
- report.md: this report. searches.jsonl contains the search command's unedited records. write_split.py is a sandbox-only generation aid, not project code.

One new node, one Mathlib leaf. No Lean files, compilation, repository writes, launcher edits or agents.

## Attachments

None. A whole-library search in lean/WeilConjectures for the blueprint tag, monic factorization and the relevant descent/division names found no declaration giving every clause of this item. The existing normalized Gauss application in ZetaLinearAlgebra/NormalizedGauss.lean is over the integers and proves neither the general normal-domain statement nor the quotient and local-coefficient clauses. The existing Mathlib declarations are tools, not project attachments.

## WANTED

No additional document is needed for this proof. The inherited provenance mentions EGA IV4, Theorem 21.14.1 (and its parent records EGA IV4 as WANTED locally). I do not claim to have read that unavailable volume or its online translation. I read Stacks algebra.tex Tag 00H6, lemma-polynomials-divide, both clauses and proof, and give an agent-written assembly of the algebraic tools. No SGA source is used.

## Corrections and scope

The item was unsplit and there was no earlier Q72 item/report. Its mathematical statement is correct as written, including non-Noetherian normal domains, repeated factors, F=1, and the local clause; no statement dispute or change is needed. I retained all inherited citations and searches and appended actual Q72 searches. The proof is marked agent-written: the last step proves the local specialization directly by convolution, rather than hiding the general radical-coefficient theorem of 00H6(2) in a citation.

The inherited blueprint ancestor is null, as tools/blueprint_refs.py ancestor reports. I preserved that ancestry and the EGA paragraph in from.place; the new node has the same ancestor and prepends this item to via. I read the chapter and unit records and the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md. This is a generic algebra tool deep below that unit; the unit's statement, steps and chapter route are untouched.

## Searches and reuse

All Mathlib searches used the required msearch.py command and their actual results are in searches.jsonl. Both natural-language services, Loogle and grep returned results. For the whole item, the first composite query and the second field-factorization phrasing find only partial tools. For the new divisor-descent node, the more focused leanfinder/leansearch queries, Loogle Polynomial.Monic, IsIntegrallyClosed, and the exact grep eq_map_mul_C_of_dvd produce a one-line specialization: put lc(G)=1 in the theorem at GaussLemma.lean:80. I read lines 50-105, including its hypotheses. The node deliberately only asserts existence of a coefficient lift; monicity and degree of the lift are checked explicitly in the item's step 2 by injectivity.

I also searched division with remainder, and read the existing DAG power-basis node before creating anything for it. The existing lem-weil-pbc-monic-quotient-free already gives the precise bases needed, so no division or quotient-injectivity node is created. The searches remain in the log and item record. Likewise lem-per-polynomial-ufd-prime-quotient already gives finite irreducible factorization and the prime quotient conclusion over a PID, and is reused at one variable over the field K. No duplicate field-factorization or irreducible-quotient leaf is created.

Before writing the new node I searched the whole DAG for the normal/monic/descent concepts, Tag 00H6, lemma-polynomials-divide and eq_map_mul_C_of_dvd, and ran blueprint_refs.py search for monic, monic divisor, 00H6, fraction field, integrally closed, irreducible polynomial and division. The returned blueprint statements do not state the new general normal-domain divisor-descent fact. The integer and subfield results are narrower in different directions. The live sources were searched as well; only the integer-specific application mentioned above was relevant.

## Not duplicates

lem-sfb-normal-monic-divisor-descent vs lem-sfb-normal-domain-monic-prime-factorization: the new node starts with one specified monic divisor G over K and only lifts its coefficients; the item constructs a finite factorization, proves domain quotients, and proves the additional local coefficient condition.

lem-sfb-normal-monic-divisor-descent vs lem-zl-monic-divisor-algebraic-coefficients: that node assumes a field extension K/k and concludes algebraicity over the subfield k; the new node permits an arbitrary normal coefficient domain A and concludes the coefficients actually lie in A.

lem-sfb-normal-monic-divisor-descent vs lem-zl-relative-algebraic-closure-polynomial-quotient-field: that node concerns a relatively algebraically closed field extension and preservation of a specified irreducible polynomial under scalar extension, with quotient-field and spectrum conclusions; the new node instead descends any specified monic divisor to an arbitrary normal domain and asserts none of those conclusions.

lem-sfb-normal-monic-divisor-descent vs lem-zl-field-extension-algebraically-closed-geometric: that node concludes geometric irreducibility of a field extension from relative algebraic closedness; it does not assert coefficient descent to a normal coefficient ring.

lem-sfb-normal-monic-divisor-descent vs lem-weil-monic-divisor-integral: that node is the special case A=Z, K=Q; it cannot supply descent for the arbitrary normal domain in this item. The new node records the general Mathlib theorem rather than duplicating the integer application.

lem-sfb-normal-monic-divisor-descent vs prop-weil-integral-rational-series: that node gives normalized integral numerator and denominator for a rational integral power series; it does not state general normal-domain polynomial-divisor descent.

lem-sfb-normal-monic-divisor-descent vs lem-sfb-complete-normal-horizontal-primes-principal: that node concerns horizontal height-one primes of a complete Noetherian normal power-series ring and uses this item's factorization; it does not state the input polynomial-divisor lifting fact. The new node depends only on definition nodes, so there is no cycle back to the power-series item.

## Review by Q72

I checked B through E of coord/delivery-errors.md against the actual node statements and sources, including the repeated B–E text in the retired-project section. The new node is self-contained, carries no proof or proof dependencies, introduces A, K, F, G and the divisor equation, cites the definitions of normal domain and polynomial ring, and writes coefficientwise image inline. Its source is Tag 00H6, label lemma-polynomials-divide, clause (1), not an unstable section number. It is a Mathlib leaf with declaration, file, line and exact specialization. JSON is written with indent=1 and a final newline; TeX has single mathematical backslashes after JSON decoding. This single-divisor lemma is a strict input to the factorization argument, not a rephrasing of the item's finite-factorization or local clauses.

For step 1 I read the full statement of lem-per-polynomial-ufd-prime-quotient. It explicitly gives finite factorization into irreducibles in a polynomial ring over any PID and says each irreducible generates a domain quotient. A field K is a PID: its only ideals are 0 and K, generated by 0 and 1. At one variable this applies to K[T]. I read Stacks 0BC1 (lemma-polynomial-ring-UFD), 034V (lemma-PID-UFD), and Mathlib Polynomial/UniqueFactorization.lean. The remaining normalization is written out, not silently inferred: divide each nonzero leading coefficient, preserve irreducibility by multiplication by a unit, and compute the total constant from the leading coefficient of F_K. Polynomial units over a field are nonzero constants, since the top coefficients of nonzero products show degrees add, and an inverse forces degree zero. Hence each irreducible has positive degree. F=1 is handled before using a nonunit factorization. Multiplicities are retained.

For step 2 I read the new node's actual statement against 00H6(1) and GaussLemma.lean:80-83. It gives exactly H with H_K=G, and does not assert an unproved factorization or quotient property. A is a domain, K is its fraction field, F is monic, and each normalized g_j is monic and divides F_K, so every hypothesis is present. Injectivity of A into its fraction field preserves the largest nonzero coefficient, so h_j is monic of the same positive degree; coefficientwise injectivity also proves the product equality. No normality of an unrelated ring, or factoriality of A, is assumed.

For step 3 I read the actual statements of def-weil-pbc-algebra-hom-quotient, lem-weil-pbc-monic-quotient-free and lem-per-polynomial-ufd-prime-quotient. The first gives the canonical quotient and its kernel, so a coefficient map sending h_j to g_j descends. The second explicitly identifies the basis as the classes of the powers of T, not merely an unspecified freeness assertion. I read Mathlib AdjoinRoot.lean:590-640 to check that this is the stated basis. Both h_j and g_j are monic of the same degree, so their bases have the same finite index set. The induced map sends sum a_i t^i to sum image(a_i) t^i; linear independence in the target and injection on coefficients prove its kernel is zero. The third cited statement really says the target quotient is a nonzero domain (no need to borrow anything from its proof). I read fields.tex Tag 09FI, example-quotient-polymial-ring, and the principal-prime equivalence in Mathlib Ideal/Maximal.lean. Finally the step spells out how a unital injection into a domain gives both nontriviality and the zero-product property. In particular I did not infer primality merely from irreducibility over a possibly nonfactorial A.

For step 4 I checked 00H6(2) but did not cite it as an unsupported theorem. Instead the whole local argument is included and elementary. Maximality gives inverses in the residue field directly. The monic factors and their complementary product stay monic on reduction, so their degrees are preserved. The coefficient of the product at the sum of the two least nonzero exponents has exactly one nonzero summand; it is nonzero over the field. Equality with T^n then forces both factors' least exponents to be their degrees. This proves that all lower coefficients vanish modulo m. It applies to each factor of the already constructed product and does not need coprimality, completeness or separability. There is no uncited radical or UFD theorem in this last elementary step.

I tested the item on F=1 (empty product), F=T, F=T^r (repeated factor T), a field regarded as a local ring with m=0, and a nonfactorial normal domain such as k[x,y,z]/(xy-z^2) over characteristic zero. The proof uses the UFD result only over K, so the last example causes no extra hypothesis. The new node allows G=1 and F=1; the coefficient lift is 1 and the statement imposes no unjustified positive-degree condition. Monicity excludes the zero polynomial in these nonzero rings. For step 4 a complementary factor can be 1, with degree and lowest exponent zero, and the same argument holds. No step exceeds 2000 characters; no long step hides an independent comparison or lemma. Every cited step/node pair is in citations.json with a verbatim quote from the actual statement.

## Unfinished work

None in this one-level split. The server dry run and direct delivery are the remaining validation/publication actions; the maintainer supplies independent review.
