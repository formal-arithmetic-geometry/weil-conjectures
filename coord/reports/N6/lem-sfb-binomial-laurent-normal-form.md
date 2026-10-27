# Stage-1 delivery: lem-sfb-binomial-laurent-normal-form

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-binomial-laurent-normal-form.json — statement, split; no full Mathlib match. Nine proof steps establish the complete original assertion. Missing definition dependencies are now explicit.
- citations.json — 18 verbatim statement quotations, one per cited node per step.
- searches.jsonl — seven actual searches by the required msearch.py command; their queries and returned declarations are retained in the item's mathlib_searches, alongside all inherited search records.
- report.md — this report. prepare.py is only a sandbox preparation script, not a project or delivery file.

New nodes: 0. New Mathlib leaves: 0. The existing polynomial-normality and localization-normality leaves suffice; no statement-only restatements of the item's clauses were created.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag, binomial/hyperbola names, xy=a, and Laurent normality. No project declaration states all clauses. The Laurent complement file provides coefficient and coefficient-map lemmas, not this theorem. Existing sorry declarations were not treated as finished proofs.

## WANTED

None for this split. The complete coefficient calculation is agent-written, as the assigned source explicitly indicates. The normality inputs are available in literature/stacks-project/algebra.tex and are already DAG Mathlib leaves. This split does not need the de Jong paper used further up the inherited chain.

## Corrections and scope

The original node had no proof. Its normality sentence followed the hypothesis “Suppose additionally that R is a domain and a is nonzero.” I have made that continuing scope explicit in the sentence itself; no hypothesis or conclusion is changed. If that sentence were instead read without the continuing nonzero hypothesis, it would be false: for R a field and a=0 the nonzero classes x and y multiply to zero. The all-ring basis assertion is still stated and proved for a=0, for zero divisors, and for the zero ring.

Added statement dependencies for quotient algebras, bases, rational functions, localizations away from an element, and Laurent polynomials. Kept all existing provenance, prior searches, chapter, unit, and inherited blueprint place/via fields. The read-only ancestor command prints `blueprint.from.node = None`; that inherited null is preserved, not replaced by an invented ancestor. The blueprint direct-image proof paragraph (3) and the parent nodal-chart split were read: this lemma supplies their local normality input and does not replace a unit route. The inherited unit record is not this lemma's statement, so its realized fields are not edited.

## Not duplicates

No new nodes. Reused lem-weil-pbc-polynomial-ring-normal-domain (Tag 030A) and lem-weil-pbc-localization-normal-domain (Tag 00GY) after opening their full statements. DAG searches by these tags, Laurent/binomial/normal-localization keywords, and whole-blueprint searches for Laurent, normal domain and binomial found no other node stating this entire calculation. The existing Laurent-ring definition is cited for coefficients and substitution; a field-only lemma was not applied to R as though R were a field.

## Review by N6

I read coord/delivery-errors.md B–E in both copies, the worker brief, stage-1 document, worker role, SETUP's chapter/unit/node hierarchy, GOAL.md, the assigned chapter and unit records, the assigned node, its nodal-chart parent, and the current blueprint direct-image proof. There was no saved item/report in this sandbox and no repair note to resume. All mutations here are confined to the assigned sandbox; no Lean, compiler or git command was run in the shared repository.

The item's source identifies the normal-form/intersection calculation as an agent argument, rather than attributing it to a Stacks theorem. I have retained that distinction in proof_origin. For the non-elementary inputs I read algebra.tex, labels lemma-polynomial-domain-normal and lemma-localize-normal-domain, and checked the tag mapping (030A and 00GY). The former assumes just a normal domain; the latter handles localization of a normal domain. Neither requires Noetherianity. I also read the pinned Mathlib instance in RingTheory/Polynomial/IsIntegral.lean, lines 179 onward, the localization lemma in RingTheory/IntegralClosure/IntegrallyClosed.lean, lines 379 onward, and the Laurent polynomial definition and localization instance. No new source or new node is needed.

For each step I opened every cited node and checked the actual sentence used:

1. def-weil-pbc-mv-polynomial-ring supplies finite monomial expansions and linearity, and def-weil-pbc-algebra-hom-quotient supplies the quotient and its kernel. The formula for N is an explicit linear map, not an asserted algebra homomorphism. The displayed finite geometric-sum identity shows each monomial minus its reduced form is in (xy-a); no division occurs.
2. Those same two definitions justify the single calculation N(xy q)=a N(q) and equality modulo the ideal. def-weil-pbc-free-module defines a basis by unique finite coefficients, exactly what the preceding calculation gives. N fixes the reduced submodule, so its annihilation of the principal ideal proves uniqueness even when a is zero or a zero divisor. This is a routine coefficient calculation, not an uncited division/Groebner-basis theorem.
3. The polynomial evaluation and quotient definitions give the displayed map. def-weil-laurent-polynomial-ring explicitly supplies uniqueness of Laurent coefficients inside K(T), including subrings R of K. Only here are domain and a nonzero used: they make R inject into K and a^j nonzero. Thus d_j a^j=0 implies d_j=0. The image is computed on the algebra generators.
4. def-weil-rational-function-field states that every rational function is P/Q with polynomial numerator and nonzero denominator. I supplied the actual denominator product d for the finitely many coefficients of both P and Q, so there is no hidden fraction-field identification or unsupported “clear denominators” step.
5. def-weil-ring-localization-away describes fractions and the kernel criterion; def-weil-laurent-polynomial-ring describes the generated Laurent ring. The proof explicitly maps each fraction into the field, checks injectivity using nonzero denominators, and gives the generators for surjectivity. In the y-chart the variable is U=a/T, whose inverse is T/a in K(T); this does not assume a is a unit of R.
6. The Laurent definition gives unique coefficients and the involutive variable change. I wrote the coefficient conditions for both rings: c_n in R and a^n c_n in R. For negative n this is divisibility by a^{-n}; for nonnegative n the second condition follows from c_n in R. These give exactly the original normal forms. This elementary finite-coefficient argument does not cite a generic intersection theorem or create a duplicate clause node.
7. def-weil-rational-function-field explicitly states the involutive automorphism T -> c/T for nonzero c in K; apply it to a. Therefore R[U] is genuinely a polynomial ring over R. The statement of lem-weil-pbc-polynomial-ring-normal-domain supplies normality of each polynomial ring, and the statement of lem-weil-pbc-localization-normal-domain supplies normality after inverting its nonzero variable. The two cited leaves apply under the hypotheses now in force. Their common fraction field is checked using the inclusions and step 4, not assumed merely from their embeddings into a larger field.
8. def-weil-pbc-normal-ring defines normality by roots of monic polynomials in the fraction field. An equation over A is literally also an equation over B and C; their normality therefore puts its root in the already computed intersection. This is a two-line application of the definition, not an unproved intersection-normality theorem.
9. The localization normality leaf applies to the complement of a prime, which excludes zero; def-weil-pbc-localization-at-prime identifies exactly that localization. This proves every asserted prime localization is a normal domain, including the generic prime.

I checked small cases directly against the formulas: a=0 gives the independent constant and pure-power monomials and is used only in steps 1–2; R=Z/4 and a=2 still satisfy N(xy q)=2N(q) without cancellation; the zero ring has exactly the unique all-zero coefficient family. For a a unit, both Laurent rings coincide, consistent with H_a being a Laurent ring. For R=Z, a=2, the T^{-j} coefficient in the intersection is precisely divisible by 2^j, whereas a positive-power coefficient has no divisibility restriction. No claim of normality is made for a nonnormal base. All proof steps are under 2000 characters. Steps 7 and 9 are marked non-elementary because they apply normality theorems; the other steps write out the elementary monomial, coefficient, localization-fraction, or monic-equation arguments rather than concealing a sublemma.

B–E checks: no new statement-only node contains a proof, no new duplicate or clause node is introduced, each cited notion is defined by its cited statement, all quotations are literal and nonempty, proof_deps is exactly the union of uses, and the existing normality leaves are tools rather than a departure from the fixed direct-image route. The required seven searches actually ran and all services responded; no failed service is recorded as absence. The full-item searches returned monic one-variable quotients, Weierstrass-coordinate bases, normal closures, and unrelated integral-scheme lemmas. A monic one-variable quotient is not this R-module normal form, and normal-closure instances do not prove that this explicit algebra is normal. No attachment or full-item Mathlib match follows.

## Unfinished work

None in the mathematical split. No new node is left for splitting. The first required server dry run passed and saved a durable completion receipt for commit f83326baf1d. The final dry run rechecks the completed report before direct delivery under the dispatcher brief; no second worker is required by that brief.
