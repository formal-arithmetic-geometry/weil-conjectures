## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-polynomial-irreducible-factorization.json: existing statement, now a Mathlib leaf; no new nodes. Match: WfDvdMonoid.exists_factors and Polynomial.isUnit_iff.
- citations.json: [] because this leaf has no proof steps and cites no proof nodes.
- report.md: this report. searches.jsonl is the search command's unmodified log.

## Attachments

None. Searched lean/WeilConjectures by the exact item id, irreducible factorization, exists_factors and algebra/field-theory declarations. No project declaration states the whole item. Mathlib declarations are recorded as a leaf, not an attachment.

## WANTED

None. The source needed for this leaf is present.

## Findings and changes

The item was unsplit with a credible mathlib_candidate and one historical grep record. I retained that record, the original statement, its two statement dependencies, source, created fields, and blueprint provenance. I promoted the checked candidate, recorded every fresh search from the actual searches.jsonl log, and supplied the declaration lines and the full inferred instance chain in mathlib_match. There is no mathematical statement correction and no unproved residue. No Lean was written and no compiler, Lake or build command was run.

The generic semantic searches returned single irreducible-factor lemmas, and LeanFinder also returned Polynomial.leadingCoeff_mul_prod_normalizedFactors. These were read as search results, not misreported as exact matches. Targeted Loogle returned WfDvdMonoid.exists_factors and Polynomial.isUnit_iff with their full types. Targeted grep confirmed lines 77, 48 and the polynomial UFD instance at 92. The two initial broad grep searches were capped at 25 results; the subsequent narrow grep found the exact factorization declaration.

## Not duplicates

No new nodes were created. The whole-DAG searches by 0BC1, WfDvdMonoid.exists_factors and irreducible-factorization wording found the existing multivariate UFD leaf lem-sfb-polynomial-field-ufd and the Noetherian factorization leaf lem-trf-factorization-exists. The former states prime factorization and uniqueness for multivariate polynomials; the latter assumes a Noetherian domain and a nonunit input and has no scalar-unit/empty-product clause. Both are related reusable tools, but this existing assigned node's statement is preserved and directly realized by Mathlib. No duplicate support node was created. Whole-blueprint search for irreducible factorization found zero nodes; the broader factorization search and latest-blueprint text search gave no statement of this field-polynomial factorization.

## Review by Q121

I read Stacks algebra.tex at lemma-polynomial-ring-UFD, lines 29578-29600; tags/tags identifies it as 0BC1. Its statement explicitly says a polynomial ring over a field is a UFD, and its proof invokes existence of irreducible factorization. This is the mathematical source of the item. I also read the current latest blueprint's sk-thm-sf-ctf-stability statement and direct-images proof (3); this elementary algebra leaf supports the inherited normal-domain monic factorization route beneath that unit, rather than replacing a geometric step. blueprint_refs.py ancestor returns None for this historical created.item chain. I kept its null ancestor and explicit EGA IV4 Theorem 21.14.1 place, rather than inventing a blueprint id; same_as remains [].

There are no proof steps to audit under C1/C4. Instead I checked each clause against the Mathlib sources: WfDvdMonoid.exists_factors, Defs.lean 77-85 (context 43-49), assumes a commutative monoid with zero with well-founded divisibility and a nonzero input. It returns a finite multiset of irreducibles and Associated f.prod P. Associated at Algebra/GroupWithZero/Associated.lean 29-30 means exactly that a unit v multiplies f.prod on the right to give P. Polynomial.isUnit_iff, Algebra/Polynomial/Degree/Units.lean 48-53 (context 28-29), says this polynomial unit is C u for a unit u in K; the required NoZeroDivisors holds because K is a field. Commutativity puts C u on the left. Enumerating the finite multiset supplies r and p_1,...,p_r without imposing distinctness. This is a change of finite-product notation, not an additional factorization theorem.

I checked the inferred instance hypotheses explicitly: Polynomial.uniqueFactorizationMonoid (RingTheory/Polynomial/UniqueFactorization.lean 92-94, context 86) applies to a commutative coefficient ring with a UFD instance. A field supplies that instance through Field.toEuclideanDomain (Algebra/EuclideanDomain/Field.lean 25), EuclideanDomain.to_principal_ideal_domain (PrincipalIdealDomain.lean 287), and PrincipalIdealRing.to_uniqueFactorizationMonoid (371-373). UniqueFactorizationMonoid extends the required well-founded divisibility at Defs.lean 135-137. Thus no Noetherian, algebraic-closure, characteristic or positive-degree hypothesis was silently added. Mathlib's Irreducible structure at Algebra/Group/Irreducible/Defs.lean 44-48 is the nonunit and unit-factor condition. Its factors are nonzero here also because their product times a unit is the nonzero P; a zero factor would make that product zero. This verifies the item's explicit nonzero irreducibility clause without an extra lemma.

I opened both statement dependency files: def-weil-field states a nontrivial commutative field and def-weil-polynomial-ring defines exactly the one-variable polynomial ring being used. The meaning of irreducible is inline, so no missing definition node is needed (B2/B3). The item has unchanged single-escaped TeX and a precise Stacks tag and label (B4/B5). mathlib_match supplies all declaration paths and lines read (B6/B8); search records are actual logged calls (B7). No new statement-only node, hidden proof, elementary node, restated clause or circular dependency is introduced (B1, B9/B10, C5-C8, D1-D5).

For edge cases (E1-E7), P=1 and any nonzero constant allow r=0 and the scalar equal to P; the empty multiset has product 1. P irreducible allows one factor, and P=T^2 over any field allows two repeated T factors. Finite fields and positive characteristic cause no change. P=0 is explicitly excluded; the zero ring is excluded by the field definition. None of these cases requires a monic hypothesis. There is no long proof step, source error, SGA citation, route departure, unfinished work or additional permission needed.

The first dry run required a non-null proof_origin even for this Mathlib leaf. I recorded the Stacks document and place already verified above; no proof steps or mathematical changes were added.
