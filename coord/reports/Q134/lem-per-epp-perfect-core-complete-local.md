# Worker report

Item: lem-per-epp-perfect-core-complete-local. Group Q134. Stage 1 only, 2026-10-19.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-epp-perfect-core-complete-local.json: split into seven proof steps; statement, statement dependencies, source, ancestry and inherited searches retained. Added actual Q134 searches and an explicit generic tool-use declaration.
- dag/nodes/sec-deligne-laumon-a1/lem-per-finite-extension-perfect-core.json: one new statement-only lemma, unsplit; no exact Mathlib match. Finite extensions preserve algebraicity of the perfect core over the base perfect core, without assuming separability.
- citations.json: six verbatim statement quotations, one for each cited node/step pair.
- report.md: this report. searches.jsonl retains the actual command results; ilo.txt is the local text of the available source PDF.

## Attachments

None. Searched the exact item tag, Epp, perfect-core and perfect-subfield terminology in WeilConjectures/ of slopmaster2 and master. No declaration states this complete-local assertion. Also searched for the new finite-extension assertion. The generic finite-generation result in GenericIrreducibility concerns a separating transcendence basis and is not an attachment. No Lean was written or compiled; master is reference material only.

## Wanted literature

None. The ILO PDF and Stacks algebra.tex are available. No SGA source is used.

## Audit and changes

The resumed sandbox had only dispatcher briefs: no item JSON, report, search log or pending delivery result. A process check found no active delivery for this item; the shared delivery log had no entry for it. I copied the current unsplit item and preserved its existing Q83 searches. The item has no substantive mathematical error and needs no statement correction. The missing work was the proof, not the statement.

I read ILO Expose IV 3.2.1, Lemma 3.2.2, Proposition 3.2.3 and its whole proof on pages 55–56, together with the application in IV 4.2.3. I also read Stacks Tag 032D, label lemma-complete-local-Noetherian-domain-finite-over-regular, including the equal-characteristic proof. This is exactly the finite Cohen parameter ring used in ILO's omitted detail in (iv). The item's parent report was checked to identify its use on complete local characteristic-p quotients. I read the current chapter, unit, ancestor statement and first proof step. This is a supporting algebra input under the ancestor's arbitrary-field duality step, not a replacement of the unit route. The chapter and unit are unchanged.

Whole-DAG and whole-blueprint searches for perfect cores, perfect subfields, finite-extension perfectness, Epp, Laurent series and the Cohen tag found no duplicate of the new assertion. The existing finite-over-regular theorem is reused. In particular, I did not create a compatible coefficient-field lemma: the actual coefficient section automatically fixes a perfect subfield by separatedness, as step 2 proves.

## Search evidence

All ten Q134 searches were run by the required msearch.py command and their hits were read. The new node records the finite-extension LeanFinder query and its second phrasing, LeanSearch, Loogle `FiniteDimensional, PerfectField`, and the perfect-core source grep, with query text copied from searches.jsonl. The item records the two complete-local/Epp LeanFinder phrasings, LeanSearch, Loogle `PerfectField, FractionRing`, and the RingTheory Cohen/perfect-core grep. The shared grep is also relevant to the item; its new searches supplement the retained earlier records. No service was unavailable.

I opened Mathlib/FieldTheory/PurelyInseparable/PerfectClosure.lean, especially its definition and the declarations at lines 70–99: perfectClosure.isAlgebraic concerns elements having some p-power in a specified base field. Our object is the intersection of all Frobenius images within one field. The type and quantifiers differ, so that hit is not an exact match or one-line specialization. Other hits concern ordinary residue-field algebraicity, perfectness of an algebraic extension of an already perfect field, finite purely inseparable exponents, Witt vectors, or semisimple operators. None gives the new assertion or the item. There are zero Mathlib leaves.

## Not duplicates

lem-per-finite-extension-perfect-core vs lem-per-epp-perfect-core-complete-local: the new lemma concerns two fields forming a finite extension and their Frobenius-image intersections; it has no local ring, completeness, residue field or specified perfect subfield. The item still proves its finite field extension, identifies the base perfect core by a Laurent-series calculation, and proves compatibility and the final algebraicity argument.

lem-per-finite-extension-perfect-core vs lem-per-coefficient-field-generic-differential-basis: the existing node constructs a coefficient section and differential parameters of a complete local ring; it makes no assertion about perfect cores in finite field extensions.

lem-per-finite-extension-perfect-core vs lem-per-mixed-reduced-special-fibre-cover: the existing node constructs a mixed-characteristic normalized cover with reduced equidimensional special fibre; the new field-theoretic lemma constructs no cover or local ring.

There are no shared Stacks tags for this new node: its source is ILO IV 3.2.2–3.2.3. The existing Stacks 032D node is cited, not duplicated.

## Review by Q134

I checked delivery-errors B–E against the files and sources, rather than treating the imported source citation as a proof. The new node introduces its fields, prime characteristic, finiteness hypothesis, perfect-core notation and polynomial conclusion. It contains statement only and no hidden proof. Its field notion cites def-weil-field, whose statement really defines a field. Its source is the finite-extension consequence of ILO IV 3.2.2–3.2.3, not a claim that the exact wording is printed there.

For the new lemma the source's minimal-polynomial argument explains why its finite hypothesis is sufficient even for inseparable extensions. For x in the perfect core choose its unique compatible roots x_n with x_n^(p^n)=x. The nested fields K(x_n) have nondecreasing degrees bounded by [L:K], hence stabilize after N. If f_n is the monic minimal polynomial of x_n, then for n>=N the polynomial obtained by raising all coefficients of f_n to p^(n-N) annihilates x_N and has the same degree as f_N. Division by the monic minimal polynomial shows it equals f_N. Thus every coefficient of f_N is in every Frobenius image of K. Raising these coefficients to p^N gives a nonzero monic polynomial over K_perf annihilating x. This is the smaller field lemma left for its own future split, not the complete-local assertion moved elsewhere.

Step 1 cites lem-weil-pbc-complete-local-domain-finite-over-regular for exactly the finite subring, power-series presentation and residue isomorphism stated there. R has all its hypotheses: Noetherian, local, a domain and maximal-ideal-adically complete. Its possible Cohen-ring branch is excluded inside the characteristic-p subring, without silently imposing characteristic zero on a coefficient DVR. The zero-constant series calculation supplies the residue field of the coefficient power-series ring; the step cites the actual coefficientwise definition of multivariate power series for this calculation.

Step 2 cites def-weil-pbc-adically-complete-ring, which explicitly includes intersection of the ideal powers equal to zero. Perfectness of the specified k0 supplies roots of every order inside the given copy of k0, not an unrelated field. The two lifts of each root have the same residue, so their difference lies in m; the displayed p-power equation makes the resulting lifts equal. This proves exactly the compatibility that an arbitrary choice of coefficient field alone would not justify. The residue isomorphism and its inverse commute with powers, so their perfect cores agree, with algebraicity over the correct copy of k0.

Step 3 is an elementary localization and finite-dimensional linear algebra calculation from step 1. It explicitly identifies the localized finite module with the actual fraction field F: a finite-dimensional domain over a field is a field by injectivity and surjectivity of multiplication. No finiteness statement is smuggled in from a parameter-map node that only supplies residue finiteness.

Step 4 cites def-weil-pbc-laurent-series for its exact coefficientwise addition, finite convolution product, bounded-below support and order. It does not cite that definition as if it already asserted a perfect-core theorem: the inverse, Frobenius coefficient formula and divisibility-of-exponents argument are all written in the step. Finite truncation after a monomial shift justifies the binomial identity for an infinite series. Both negative and positive exponents vanish unless zero, and the constant coefficient has roots in H itself.

Step 5 cites def-weil-pbc-multivariate-power-series for the families of coefficients and finite convolution. Grouping those coefficients embeds the ring into the stated iterated Laurent field, and the fraction map is written explicitly. Applying step 4 repeatedly identifies K_perf with C_perf; roots of elements of K remain roots under that embedding. The reverse inclusion uses constant roots in C. No equality of a perfect closure with a perfect core is used.

Step 6 cites lem-per-finite-extension-perfect-core, whose statement explicitly applies to an arbitrary finite field extension in characteristic p and concludes algebraicity over the base perfect core. F/K is finite by step 3, and its base perfect core was identified in step 5. No separability is needed or assumed.

Step 7 is the elementary finite-coefficient argument for transitivity, rather than an uncited invocation of an algebraic-extension theorem: choose monic equations over k0 for the finitely many coefficients, reduce exponents, and obtain a finite spanning set containing all powers of x. Linear dependence supplies the required nonzero k0 polynomial. The relevant k0 is the specified one by step 2.

The six entries of citations.json cover exactly these cited step/node pairs; each quote is copied verbatim from the current cited statement. The sole off-unit result is the generic Cohen parameter theorem; its necessity is declared in split_report.tool_uses for maintainer review, not installed in the maintainer-owned tool_uses field. All seven proof steps are shorter than 2000 characters. The Laurent computation and coefficient compatibility are routine explicit calculations, not hidden standard lemmas.

Small cases were tested: R=k is d=0 and gives the original residue assumption; R=k[[t]] gives K_perf=k_perf by the coefficient calculation; imperfect k is allowed. The hypothesis on k_perf is necessary when R=k has a perfect transcendental extension of k0 as residue field. In the new node L=K gives the identity case, finite constant extensions such as F_(p^2)/F_p are allowed, and K=F_p(t), L=F_p(t^(1/p)) tests an inseparable extension. Replacing finite by merely algebraic would be false: the perfect closure of F_p(t) has perfect core containing t, transcendental over the perfect core F_p of F_p(t). The node retains the essential finite hypothesis.

The preliminary server review_split check passed. The final full delivery dry run is run after this report; its success and the actual push are the remaining gates.

## Unfinished work

No unfinished part of the item's split. The one new auxiliary remains unsplit as required by one-level delivery. No compiler, Lake, build, agent delegation or changes to the shared repository or launcher were used in producing the delivery files.
