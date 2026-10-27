# Stage-1 report: lem-trf-product-minpoly-spectral-maximum

## Files written

- dag/nodes/sec-trace-formula/lem-trf-product-minpoly-spectral-maximum.json: unchanged statement, split into three steps; no Mathlib match for the whole item.
- dag/nodes/sec-trace-formula/lem-trf-polynomial-weighted-gauss-multiplicative.json: statement; Mathlib leaf, Polynomial.gaussNorm_mul at Mathlib/RingTheory/Polynomial/GaussNorm.lean:276, with the absolute-value hypotheses at 219–221 and definition at 49–50.
- dag/nodes/sec-trace-formula/lem-trf-finite-algebra-minpoly-properties.json: statement; Mathlib leaf, one declaration per clause: IsIntegral.of_finite (IntegralClosure/Algebra/Basic.lean:64), minpoly.monic (Minpoly/Basic.lean:54), minpoly.aeval (:89), minpoly.natDegree_pos (:192), minpoly.dvd (Minpoly/Field.lean:69).
- citations.json: one exact statement quotation for each node used in each proof step.
- searches.jsonl: actual msearch.py results, retained without rewriting.

## Attachments

None. Searching all lean/WeilConjectures for the blueprint tag, spectralValue, spectralNorm, and minpoly/product keywords found no project declaration giving this item. The leaf matches are Mathlib declarations, not project attachments.

## Wanted literature

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, proof of Lemma 5.3.3/4, printed p.217 (scan PDF p.223), and Section 3.1.2, for lem-trf-product-minpoly-spectral-maximum. The archival PDF named by the inherited node is absent from literature/. Opening the inherited primary scan URL with the web tool failed because the 14,153,572-byte PDF exceeded its fetch limit. I did not claim to read that scan. Its pinpoint is retained as inherited metadata. The proof is explicitly agent-written from the locally read Mathlib inputs, not attributed to an unread BGR proof.

## Problems found and corrections

The imported item has no proof, and its finite-product coefficient radius does not follow directly from Pi.spectrum_eq: that is the algebraic spectrum over K and need not see roots over extensions. Nor may spectralNorm multiplicativity with a complete nontrivially normed base be used when the item assumes neither hypothesis. Instead I used the weighted Gauss norm on polynomials, whose multiplication theorem assumes only a nonarchimedean absolute value and a positive real weight. No statement correction or STATEMENT-DISPUTED is needed.

The product minimal polynomial is not generally the product of the coordinate minimal polynomials. I use only p_j divides p and p divides Q=product p_j. This covers repeated coordinate polynomials without a coprimality or separability claim. The monic quotient may be 1, so the proof explicitly sets s(1)=0. The positive test weight r ranges over all positive real numbers, not only values attained in K; this also covers a trivial absolute value.

The current latest blueprint was read at literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/{_section.md,lem-trf-local-term-locality.md,lem-trf-local-term-locality.proof.md}. Its contracting-correspondence route is unchanged. This is the independent analytic supporting input already assigned to this item by its historical ancestry, below the unit level. The item is not the unit's key node, so no unit realization file was changed.

## Not duplicates

lem-trf-polynomial-weighted-gauss-multiplicative vs lem-trf-tate-gauss-multiplicative: the new leaf is for finite univariate polynomials at any positive real weight, the existing node is for restricted multivariate series at weight 1; passing between them would require introducing that restricted-series model.
lem-trf-polynomial-weighted-gauss-multiplicative vs lem-trf-weighted-disc-banach: the latter assumes completeness and proves a weighted series Banach algebra, with only a submultiplicativity conclusion, not this polynomial multiplicativity theorem.
lem-trf-polynomial-weighted-gauss-multiplicative vs lem-trf-tate-unit-coefficient-criterion: that is a unit criterion in complete Tate algebras, not this polynomial norm statement.
lem-trf-finite-algebra-minpoly-properties vs lem-trf-incomplete-spectral-algebra-norm: the latter concerns the spectral norm in an algebraic field extension, not the monic/divisibility properties in an arbitrary nontrivial finite algebra such as a product.
lem-trf-finite-algebra-minpoly-properties vs lem-sfb-endomorphism-minpoly-scalar-extension: that concerns change of scalar field for linear endomorphisms, not the stated basic minpoly clauses.

Before creating these nodes I searched the entire dag/nodes tree by gaussNorm_mul, weighted Gauss, minpoly.dvd, monic/divisor and annihilator terms, and used tools/blueprint_refs.py search for Gauss, gaussNorm_mul, minimal polynomial, minpoly.dvd, annihilating, and spectral. I read the promising statements; none states either new node. The new ids were absent from the DAG and Lean source. There is no new Stacks-tagged node; the primary sources for the leaves are Mathlib declaration files, with exact line numbers rather than invented Stacks attributions.

## Review by NS

I read the item, its chapter and unit, the current blueprint ancestor, the finite-algebra and Gauss-norm Mathlib sources, and delivery-errors B–E. The BGR archival gap is stated above. Every new node is self-contained and statement-only, has an empty proof and proof_deps, and names field and polynomial definition nodes. Each Mathlib hit was checked against the source type, including the surrounding section hypotheses, rather than accepted from a search name alone. I checked def-weil-field and def-weil-polynomial-ring directly; they give the notions cited by the statements. New nodes inherit the chapter, unit, and nearest-blueprint-ancestor chain, with exact supporting places and no same_as matches.

Step 1 uses lem-trf-finite-algebra-minpoly-properties. Its statement supplies existence, monicity, positive degree, vanishing, and divisibility for arbitrary nontrivial finite algebras, so it applies both to each field and to the finite product. Nonempty I makes that product nontrivial; coordinate spanning sets show finite dimension explicitly. The step itself writes out coordinate evaluation and the two divisibilities. In particular it does not cite a field-only irreducibility statement for the product algebra.

Step 2 uses lem-trf-polynomial-weighted-gauss-multiplicative. Its statement gives exactly G_r(fg)=G_r(f)G_r(g) for the same positive real r and the given absolute value. The rest is the displayed coefficient comparison: G_r(f)=r^d iff all |b_i| are at most r^i, and if h=fg is monic then the lower bound G_r(g)>=r^deg(g)>0 permits division. This is a routine elementary estimate from the cited theorem and definitions, not an uncited norm-extension theorem or splitting-field argument. The final passage to s(f)<=s(h) is justified by an explicit midpoint contradiction, including s(h)=0.

Step 3 uses the same Gauss multiplication statement repeatedly over the finite set. The coefficient criterion from step 2 gives the value for each factor and then for Q. Taking every r>M, rather than r=M, prevents a division by zero when M=0. The previously established divisibilities bound s(p) above by s(Q) and below by every s(p_j). The final maximum exists because I is nonempty finite. The proof is an assembly of these explicit estimates, not an application of a new node repeating the item. All steps are under 2000 characters; none hides an independent comparison or a source's omitted argument.

I tested the relevant boundaries mathematically. For a singleton the result is the identity. For x=0 all minimal polynomials are Z, Q is Z^|I|, and every radius is 0. Repeating a coordinate polynomial creates repeated factors in Q but does not change either inequality. If some coordinates vanish and others do not, those factors contribute radius 0 and still have degree 1. For a trivial absolute value every nonzero coefficient has value 1, and the proof remains valid by testing arbitrary positive real weights. Purely inseparable minimal polynomials such as Z^p-a are allowed: neither divisibility nor Gauss multiplication needs distinct roots. The finite-algebra leaf deliberately excludes the zero algebra, whose minpoly would be 1; its nontriviality hypothesis is checked in step 1. The Gauss leaf permits zero factors, which the Mathlib source also permits, while all factors actually used here are monic nonzero. No completeness, nontrivial valuation, normality, separability, or algebraic closure is introduced. No SGA source is used.

The search records are the actual msearch.py queries and outputs. The item retains its prior search history and adds the current searches. The new leaves have leanfinder, loogle, leansearch and grep evidence; no service failure was interpreted as absence. citations.json quotes the exact statement strings for the two used nodes. This review is my own author check for direct delivery; the maintainer's independent review remains the acceptance step.

## Unfinished work

No mathematical split remains unfinished. The archival BGR source is wanted as above. Only stage 1 was performed: no Lean file was written, no compiler or Lake was run, and no repository or launcher file was edited.

## Validation repairs

The first delivery dry run required the numeric mathlib_match.line field in addition to the verified line locations already written in source.place and how. I added 276 for the Gauss theorem and 69 for the minpoly divisibility theorem; the per-clause locations remain in how. No mathematical content changed.
