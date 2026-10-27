# Stage-1 report: lem-sfb-monic-principal-open-fppf

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-monic-principal-open-fppf.json: item split into four steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-basic-open-image-coefficients.json: statement, Mathlib leaf, exact match Polynomial.mem_image_comap_C_basicOpen in Mathlib/RingTheory/Spectrum/Prime/Polynomial.lean:141–149.
- citations.json: verbatim statement quotations for all eight citations in the four steps.
- searches.jsonl: actual msearch.py queries and outputs; inherited item searches retained in its JSON.

## Attachments

None. Searches for the item's blueprint tag and for monic principal opens in lean/WeilConjectures found no declaration proving every clause. Polynomial relation and separable-model constructions do not give this theorem. The new image criterion is a Mathlib declaration, not a project attachment.

## WANTED

None.

## Corrections and route

The imported statement is correct, including its explicitly written monic presentation over the zero ring. There was no proof to retain. No hypothesis, conclusion or definition was changed. Mathlib search hits for monic polynomial images concerned either openness of an image or universal factorization algebras and did not state the full fppf theorem. A second semantic phrasing found the precise general coefficient criterion. The item therefore remains a split, while that strictly more general prime-image criterion becomes a Mathlib leaf.

Read GOAL.md, the stage-1 contract, the three levels in SETUP.md, and delivery-errors B–E in both copies. Read the chapter and unit records, and the current latest blueprint direct-images proof paragraph (3), under literature/blueprint/latest (COMMITS.txt records main-20261024). This auxiliary algebraic input sits far below that paragraph along the inherited Conrad group-scheme chain; it changes no unit or chapter route. blueprint_refs.py ancestor prints None because the inherited created.item chain has no marked blueprint ancestor. Its existing null from.node and full from.place are retained; the new leaf prepends this item to the inherited via chain. This is an existing ancestry limitation, not a fabricated ancestor.

## Not duplicates

lem-sfb-polynomial-basic-open-image-coefficients vs lem-sfb-monic-principal-open-fppf: both cite Tag 00FB, but the new Mathlib leaf states the coefficient criterion for the image of D(f) for every polynomial, without a monicity hypothesis or any flatness or finite-presentation assertion. The item applies this criterion to coefficient 1 and proves the two other properties separately. This is not a node restating surjectivity for monic polynomials.

Whole-DAG searches by 00FB, affineline-open, imageOfDf, mem_image_comap_C_basicOpen, image_comap_C_basicOpen, and polynomial/flat/localization names found no existing node stating this coefficient-image criterion. Whole-blueprint searches for monic, coefficients polynomial, and monic principal open fppf likewise found no equivalent blueprint statement. The principal-open spectrum identification, polynomial projection flatness, localization flatness, affine flatness criterion and composition theorem were all reused. Hits for polynomial good-locus localization concern freeness and finite presentation of modules, not images of D(f).

## Review by Q05

I read algebra.tex Tag 00FB, lemma-affineline-open, including its complete proof: its final coefficient image formula is the source both of the item’s surjectivity argument and the new leaf. I read the new leaf’s Mathlib proof at Polynomial.lean:141–149 and the equivalent imageOfDf definition and theorem at IsOpenComapC.lean:35,52. The former exactly says that a prime lies in the image of D(f) iff one coefficient is outside that prime; it assumes only CommRing, with no field, degree, nonzero, or finiteness hypothesis. I checked the searches and read their hits before choosing this exact declaration.

Step 1 uses the actual statement of lem-weil-pbc-localization-away-polynomial-quotient, not an assertion buried in its proof. It states surjectivity, the kernel (rx-1), and the resulting algebra isomorphism. Substitute B=A[T] for R and P for r; its map fixes B, so the isomorphism respects the given base A and hence the morphism in the item. The source is the localization presentation in Tag 08JZ. This also avoids treating a quotient as a localization without justification.

Step 2 uses lem-nagata-polynomial-projection-flat for one variable, lem-weil-pbc-localization-flat for B at powers of P, lem-weil-pbc-flat-ring-map-iff-flat-affine to pass from that ring map to its spectrum morphism, and lem-pc-flat-compose for their composite. I opened and read each statement: the projection lemma allows any commutative base and any variable set, the localization statement permits a multiplicative subset containing zero, the affine criterion is an equivalence for arbitrary commutative rings, and the composition statement has precisely the two flat maps now established. I read the supporting algebra.tex Tag 00HT statement (localization flatness) and morphisms.tex Tag 01U5 statement (affine characterization). No regularity, Noetherianity, faithful-flatness or nonempty-spectrum hypothesis is used.

Step 3 cites def-sbc-locally-finite-presentation, which explicitly defines the property using affine neighbourhoods and a finite-generator finite-relation quotient. I read morphisms.tex Tag 01TP, definition-finite-presentation. The whole source and target are permitted affine neighbourhoods, and the item already displays exactly two generators and one relation. This is a direct application of the definition, so it is elementary and needs no new finite-presentation lemma.

Step 4 uses lem-weil-pbc-spec-localization-away-basic-open, whose clause (ii) identifies the localization spectrum with D(P), and the new coefficient-image leaf. I read both statements in full. The former is a homeomorphism with its map given by contraction; the latter’s projection is also contraction, so their composite is the original coefficient map. The coefficient of T^d is 1 by the item’s explicit monic expression, and primes are proper, so every prime is in the image. This is a surjectivity proof over arbitrary rings, not a rational-point argument over a finite field. I checked d=0: P=1 and the quotient is A[T], not A. For A=0 both spectra are empty, so surjectivity and the local conditions hold vacuously. As additional tests of the new general statement, f=0 gives an empty image and no witnessing coefficient, while f=1 gives the entire image; over a field any nonzero f gives the unique base prime. No excluded small case was needed.

All non-elementary steps cite theorems that say exactly what they use. citations.json records each cited statement verbatim. No step is longer than 2000 characters (lengths 329, 410, 324, 611), and no argument has been hidden in a new unsplit statement. The only new node is an exact Mathlib leaf, with its source tag, declaration, file, line, notions and searches recorded. I checked delivery-errors B–E against these files: self-contained statements, no proof in the new leaf, no doubled TeX escapes, no duplicate, no item-clause relabelling, no new axiom or unproved existence assumption, and no circular citation. Every statement cited outside this unit is already a Mathlib leaf and is a generic tool under the contract.

## Unfinished work

None in the mathematical split. The independent maintainer review and landing remain the maintainer’s responsibility after this direct delivery.
