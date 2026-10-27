# Stage-1 report: lem-sfb-prime-cyclotomic-degree-norm

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-prime-cyclotomic-degree-norm.json: item, statement unchanged, split into four steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-prime-root-shift-minpoly.json: statement, Mathlib leaf. Direct rewrite of minpoly.sub_algebraMap, Polynomial.cyclotomic_eq_minpoly_rat and Polynomial.cyclotomic_prime; all file/line locations are recorded in mathlib_match.how.
- citations.json: one verbatim statement quote for every node cited by every step.
- searches.jsonl: unaltered outputs recorded by msearch.py; queries and actual summaries copied into mathlib_searches. The new node was kept in mind as lem-sfb-prime-root-shift-minpoly when these searches ran.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag and for cyclotomic norms, primitive-root minimal polynomials and shifted minimal-polynomial names found no project declaration giving the item. The relevant results are in Mathlib, not attachments.

## WANTED

None. Milne's Abelian Varieties PDF is available. Its reference to ANT Chapter 6 is resolved here by the Mathlib minimal-polynomial results, whose source was read, rather than adding an unsourced irreducibility assertion.

## Findings and changes

The original unsplit node has the correct statement, including the negative norm at p=2. I preserved its statement, source, created record, chapter, unit and all inherited blueprint metadata. The inherited blueprint.from.node is null; tools/blueprint_refs.py ancestor prints None. I preserved that result and inherited via chain instead of inventing a blueprint ancestor. I read the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md; paragraph (3) is the direct-image route for which this inherited alteration/level-rigidity prerequisite was introduced. No unit or chapter record is changed.

The node's previous Mathlib candidates require assembling the generated cyclotomic field and treating 2 separately. This delivery uses Milne's minimal-polynomial route. The translation theorem minpoly.sub_algebraMap does not assume that the ambient field itself is cyclotomic. Thus the one new polynomial leaf applies directly in E or K, with no finiteness assumption on K, and its one-line rewrite avoids that candidate's setup issue.

## Not duplicates

lem-sfb-prime-root-shift-minpoly vs lem-sfb-prime-cyclotomic-degree-norm: the new leaf identifies a minimal polynomial and states neither the field degree nor the norm; the item's steps compute those from this polynomial using existing generic results.
lem-sfb-prime-root-shift-minpoly vs lem-sfb-finite-field-norm-minpoly: the existing leaf computes a norm from an unspecified minimal polynomial; the new leaf identifies the particular polynomial and does not state any norm formula.
lem-sfb-prime-root-shift-minpoly vs lem-weil-pbc-minimal-polynomial-quotient-field-iso: the existing leaf identifies a quotient for an unspecified algebraic element; the new leaf identifies a polynomial for a root of unity.
lem-sfb-prime-root-shift-minpoly vs lem-sfb-integral-minpoly-fraction-descent: the existing leaf descends coefficients over integrally closed domains and does not identify any cyclotomic polynomial.

I searched all DAG statements for cyclotomic and shifted-root/minimal-polynomial facts, declaration names and source phrases, and ran blueprint_refs searches for cyclotomic, minimal polynomial and shifted. The blueprint cyclotomic hits concern Tate twists and additive characters; none identifies this minimal polynomial. No new Stacks-tagged node is introduced. Generic field-presentation and quotient-basis leaves already exist and are reused.

## Review by NE

I read Milne, Abelian Varieties, Chapter I Lemma 14.5, printed p.63 (PDF p.69), with the displayed polynomial and the signed norm equation. This is the source for the item and the new node. I also read the actual Mathlib hypotheses and proofs at FieldTheory/Minpoly/Field.lean:174-193, RingTheory/Polynomial/Cyclotomic/Roots.lean:178-191, and RingTheory/Polynomial/Cyclotomic/Basic.lean:367-373. The leaf is a direct rewrite: translate by 1, identify the unshifted rational minimal polynomial, expand the prime cyclotomic polynomial, and distribute composition over sum and powers. Exact order p supplies IsPrimitiveRoot, p is positive, and characteristic zero gives the rational algebra. The stronger IsCyclotomicExtension hypothesis on the initially found minpoly_sub_one_eq_cyclotomic_comp is unnecessary; I corrected the candidate approach to use the general translation theorem instead. No new proof is written in the leaf.

For step 1 I opened the new node and checked that it states exactly the minimal-polynomial equality used. Applying it in E is legitimate because E is a characteristic-zero subfield of K and the same powers of eta have the same equalities there. The minimal polynomial is defined in the leaf as monic and annihilating the element, so P(x)=0 is part of its statement, not an appeal to an unstated property.

For step 2 I opened def-weil-polynomial-ring: it defines degree as the largest nonzero exponent and constant coefficient as evaluation at zero. Only the highest summand contributes to degree p-1, with coefficient 1; substituting zero into each summand gives 1. This is a polynomial calculation written in the step, not a separate lemma. Primality gives p>=2, so no empty sum or negative index occurs.

For step 3 I opened lem-weil-pbc-minimal-polynomial-quotient-field-iso and lem-weil-pbc-monic-quotient-free. The former states the evaluation isomorphism to the smallest generated subfield for any algebraic element, and the latter states the full power basis for a monic polynomial quotient. These are exactly the claims taken from them. The explicit equalities x=eta-1 and eta=x+1 identify Q(x) with E. P is a nonzero annihilator by steps 1-2, so the algebraicity hypothesis holds; P is monic of degree p-1, so the quotient-basis hypothesis holds. Transporting this stated basis along the stated linear isomorphism proves the degree. I did not use the power-basis leaf's search notes as if its statement said degree equals minimal-polynomial degree: the chosen two leaves state the needed presentation and basis directly.

For step 4 I opened lem-sfb-finite-field-norm-minpoly. Its statement explicitly defines the determinant norm and gives ((-1)^m P_x(0))^e for arbitrary finite field extensions without a separability assumption. Step 3 has established finiteness. Here Q(x)=E, so the remaining degree is dim_E E=1 (basis {1}). Substituting the computed degree and constant term gives the claimed signed p. I also read Stacks fields.tex, lemma-degree-minimal-polynomial (09GN) and lemma-trace-and-norm-from-minimal-polynomial (0BIH), to check the standard presentation/norm route. The norm formula is used from the existing node's statement, not its proof.

I tested p=2 with eta=-1: P=T+2, E=Q, degree 1 and norm -2. For p=3 the polynomial is T^2+3T+3, degree 2 and norm 3. For p=5 it is monic of degree 4 with constant term 5, giving norm 5. A larger or transcendental ambient K causes no issue because the proof takes place in E. The hypothesis prime excludes p=0 and p=1; characteristic zero prevents collapse of the rational coefficients. The item's statement is true and needs no dispute correction.

Against delivery-errors B-E: the new node is self-contained, statement-only, and cites the field-extension and polynomial definitions. Its Mathlib match names each read declaration, file and line; recorded searches were actually run with msearch.py, including a second phrasing. No elementary calculation or clause of the item has been repackaged as a new node. Every non-elementary step cites statements that supply what it uses, and citations.json contains their verbatim text. All proof dependencies are exactly the union of uses, with no back edge: the new polynomial leaf depends only on definitions. The off-unit statements used are already Mathlib leaves. All four steps are below 2000 characters, and none hides an additional comparison or standard lemma. No SGA source is used. No Lean was written and no compiler, Lake or local project checker was run.

## Unfinished work

None in the authorized stage-1 split. The required server dry run and delivery are the final validation steps.
