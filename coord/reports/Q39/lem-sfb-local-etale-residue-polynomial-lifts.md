# Q39: lem-sfb-local-etale-residue-polynomial-lifts

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-local-etale-residue-polynomial-lifts.json: statement, split; eight complete proof steps, with the imported statement and statement dependencies preserved. No new nodes, and no new Mathlib leaves.
- citations.json: one verbatim statement quotation for each of the 24 citations in the item's numbered proof steps.
- searches.jsonl: five actual searches through msearch.py, retained without alteration. The item records their queries and results in addition to its inherited searches.
- report.md: this report.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for residue-polynomial and polynomial-lifting terminology. The exact tag has no hit. The nearby files FlatLocalMonogenicExtension.lean and EtaleGenericResidueFieldModel.lean concern a single local flat extension or an etale neighbourhood with prescribed residue field, respectively. Neither states this item's finite Galois envelope, finite free etale monic quotient, and complete generic field decomposition. They are not claimed as attachments. No Lean was written or compiled.

## Wanted literature

WANTED: de Jong, Families of curves and alterations (1997), Lemma 5.6, printed p.614, for lem-sfb-local-etale-residue-polynomial-lifts. The inherited source path literature/de-jong-families-curves-alterations-1997.pdf is absent on this machine. I did not download it. The proof is explicitly marked agent-written, using the available Stacks algebra.tex construction and existing DAG statements rather than claiming to have read de Jong's omitted proof.

## What was wrong or incomplete

The imported item had a statement and searches but no proof. Its statement is correct as written: the local-ring assumption is strong enough to turn the usual derivative-localized standard-etale algebra into the whole monic quotient. I supply that justification with the existing Nakayama node, not with an assertion that an arbitrary polynomial lift is already etale. There is no statement dispute and no change of route. The existing blueprint provenance has from.node = null; tools/blueprint_refs.py ancestor confirms None. Its explicit place and via list are preserved, and no fabricated ancestor is supplied.

## Mathlib and duplicate searches

Ran the required search command for the whole item, with both formulations:

- leanfinder: "A monic polynomial over a local ring whose reduction is separable defines a finite free etale algebra with power basis". Hits include StandardEtalePair.instEtaleRing, Algebra.IsStandardEtale and StandardEtalePresentation; these require already prepared derivative-unit data and do not state the whole item.
- loogle: "Polynomial.Monic, Algebra.Etale". The factorization-neighbourhood lemma Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime concerns a different construction.
- grep: "basis.*[Pp]ower|basis.*[Mm]onic|[Mm]onic.*basis|isUnit.*(maximalIdeal|residue)|isUnit_of.*[Ff]inite", subdirectory RingTheory. Returned power-basis material, not the whole construction.
- leansearch: "A monic lift of a separable residue polynomial over a local ring is finite etale". Returned standard-etale, separable-field and polynomial-lifting facts, not a match for every clause.
- leanfinder: "If a monic polynomial has separable reduction modulo the maximal ideal then its derivative is a unit in the quotient algebra". Returned derivative and separability facts; I instead assemble existing DAG nodes and write the Nakayama application out.

Searches of the whole DAG by tags 00UD and 00U3 and by the notions monic quotient, finite Galois envelope, primitive element and integral stalk found existing nodes for all the needed facts. Blueprint searches "separable polynomial" and "finite Galois" found only def-kun-separably-closed and no match, respectively. Therefore no new node was created. In particular the existing lem-weil-pbc-monic-quotient-free, lem-weil-pbc-finite-galois-receiving-separable-extensions, lem-weil-pbc-standard-etale-monic-derivative and lem-weil-pbc-etale-algebra-over-field-product are reused. The residue-polynomial-lift node for a general prime scales the primitive element to clear denominators; here surjectivity R -> F allows direct coefficient lifts, so there is no need to import that extra construction.

## Not duplicates

No new nodes. Every constituent with an existing statement is cited directly.

## Review by Q39

I read coord/delivery-errors.md B--E and checked the actual steps against the cited statements, not against their proofs. I read the available Stacks sources algebra.tex at lemma-etale-over-field (00U3), lemma-make-etale-map-prescribed-residue-field (00UD), definition-standard-etale (00UB), lemma-standard-etale (00UC), and lemma-NAK (00DV), together with morphisms.tex lemma-finite-type-noetherian (01T6) and fields.tex lemma-normal-closure (09DT) and lemma-normal-closure-galois (0EXM). The current blueprint direct-images proof paragraph (3) and the inherited unit record confirm that this local field-algebra preparation remains below the prescribed direct-image route. No forbidden SGA route was used.

Step 1 uses finite-type-over-Noetherian to obtain a locally Noetherian affine chart, pqf-def-locnoeth for the chart's meaning, spec-domain-stalks-function-field for its localization, and localization-noetherian for that localization's Noetherian property. Integral-scheme-stalks-in-function-field gives exactly a domain and its fraction field, without needing normality. def-weil-residue-field states the local-ring quotient defining F. The field base has only two ideals and one spectral point, so the Noetherian base hypothesis is satisfied; no assumption that s is closed in S is made.

Step 2 uses finiteness to get affineness over Spec F, the affine-spectrum definition to identify the section algebra, and the existing etale-algebra-over-field-product node for every finite separable factor. That node allows the zero algebra, so the empty case is covered. Step 3 applies the existing finite-Galois-receiving-separable-extensions node to this finite family; its conclusion includes separability and normality, not just a normal envelope. The maps from fields into a nonzero field are injective by the explicit kernel argument. The primitive-element and minimal-polynomial-quotient nodes give the generator, positive degree and quotient identification. Separability of q is precisely part of def-weil-pbc-separable-algebraic-extension. The Galois-envelope citation is recorded as a generic off-unit tool, not a replacement for the unit's route.

Step 4 lifts only the finitely many lower coefficients, retaining the leading coefficient 1. The monic-quotient-free statement explicitly gives both the power basis and the reduction isomorphism; I do not take either from a hidden proof. Step 5 obtains the Bezout identity from def-pc-separable-polynomial, uses the power-basis statement to prove that C/uC is finite, and verifies every hypothesis of nakayama-jacobson: I is the unique maximal ideal, hence is the Jacobson radical, and multiplying the lifted Bezout identity proves M = I M. This yields 1 in uC and thus a genuine inverse of the derivative. It avoids assuming henselianity and does not claim that a chosen lift of a residue inverse is already an inverse.

Step 6 invokes the standard-etale-monic-derivative node exactly for its localized algebra. The two maps on T and Y are written down, and uniqueness of an inverse proves the isomorphism with C after step 5. Its finite-module condition is supplied by the existing monic power basis. Step 7 writes the tensor/quotient identification by maps on generators, invokes the affine-fibre-product node for the actual scheme fibres, and uses etale-base-change-finite-limits only for the etaleness of this base change. The etale-algebra-over-field-product statement then gives the generic separable fields. The positive-rank power basis over nonzero K rules out the empty product; the statement does not incorrectly claim that the generic algebra is a field.

Step 8 checks the exceptional empty case directly: the identity extension, polynomial T, quotient R and singleton generic factor all satisfy the requirements. I also checked a rational residue extension (degree one), positive residue characteristic (the separable Bezout identity still holds), the generic point s (R is already a field), and a nonclosed s. None requires a perfect base field, a henselian local ring, or normality of S. The quotient argument works for arbitrary monic lifts of the chosen q. All new work is in the sandbox, and every non-elementary step has actual cited statements. No step exceeds 2000 characters, and no clause has been moved into a new node. The report and citations preserve the full argument for the maintainer's independent review.

## Unfinished work

None in the stage-1 mathematical split. Required dry-run and delivery results are recorded below after execution.
