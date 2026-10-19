## Files written

- `dag/nodes/sec-trace-formula/lem-trf-refined-noether-normalization-prime.json`: statement, split into nine induction steps; no Mathlib match for the whole prescribed-prime normalization. Its statement is unchanged.
- `dag/nodes/sec-trace-formula/lem-trf-polynomial-shear-leading-coefficient.json`: new statement-only lemma, Stacks 051N; unsplit, no match in the installed Mathlib.
- `citations.json`: 18 verbatim excerpts (whole statements for the short tools), one for every citation of every step.

The sandbox initially had only dispatcher brief markers. I copied the current item and retained all inherited Q69 search records and its blueprint ancestry. New executed searches are retained in `searches.jsonl`. No Lean was written or compiled, and no live repository or launcher file was modified.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` found no declaration tagged with the item and no exact prescribed-prime refinement by concept. The Noether-normalization extensions there prove ordinary or generic relative normalization and finite flat charts, which do not prescribe this contraction. The archived upstream master is not used as proof evidence.

## WANTED

None. All mathematical sources used are present locally.

## Corrections and source audit

The item had no proof. Its source statement agrees with algebra.tex, Tag 051P, label `lemma-refined-Noether-normalization`, lines 28074–28122. The source writes a finite ring map, but all its coordinate constructions fix the field, so the item's assertion of a finite k-algebra map is faithful. The source says the chosen polynomial is monic over k[x_1,...,x_n]; here the intended coefficient ring is k[x_1,...,x_{n-1}]. The steps use that coefficient ring and explicitly multiply the transformed polynomial by the inverse of its scalar leading coefficient. These are clarifications of the source proof, with no changed mathematical statement and no statement dispute.

I read `dag/chapters/sec-trace-formula.json`, `dag/units/sk-i-curve-zero.json`, and the recorded ancestry to `lem-trf-local-term-locality`. The item is a lower-level commutative-algebra ingredient of the recorded polynomial chart and flattening route. It is not a statement-bearing node of the unit, so no unit realization field is changed. No SGA source is used.

The installed NoetherNormalization.lean has private `T` and `T_leadingcoeff_isUnit` over fields (lines 87 and 143), inspected with the surrounding proof at lines 90–169. Loogle's public `NoetherNormalization.varChange_leadingCoeff_isUnit` belongs to its online index and is absent from this installed file: the required msearch source grep returned only the private older helpers. Moreover that theorem concerns unit leading coefficients over fields, whereas 051N asserts that the scalar leading coefficient is an original nonzero coefficient over any commutative ring. The new node states precisely the useful polynomial helper from the source, and does not assert a normalization map or any contraction of primes. Its mathematical content is strictly smaller than the item.

## Not duplicates

- lem-trf-polynomial-shear-leading-coefficient vs lem-trf-refined-noether-normalization-prime: the former concerns the leading term after a polynomial substitution over any commutative coefficient ring; it asserts neither a finite polynomial map nor control of a prime ideal. The latter is proved by induction using that leading-term lemma.
- lem-trf-polynomial-shear-leading-coefficient vs lem-zl-noether-normalization-field: the existing ordinary-normalization node gives a finite injective map into a finitely generated field-algebra; it does not give this explicit triangular substitution or its leading coefficient over an arbitrary ring.

Before creating the helper I searched the whole DAG for 051N, `lemma-helper-polynomial`, triangular automorphisms, monic coordinate changes, and polynomial shear terminology, and used `tools/blueprint_refs.py search` for 051N, triangular, monic, and Noether normalization. There is no corresponding node or blueprint statement. The ordinary normalization, rational-function, and triangular field-model hits have different statements. The ancestor command returns `lem-trf-local-term-locality`; the new node's via list inserts the item ahead of the retained ancestry. Its from.place describes the exact helper-polynomial application inside 051P used by the affine polynomial chart. Same-as lists remain empty.

## Unfinished work

Only the new statement-only 051N node remains for a later worker. Its proof is intentionally not split here. The source proof reduces to distinct weighted monomial degrees: choose powers of a base exceeding the exponents in the finite support, so distinct exponent tuples have distinct weighted degrees. Expanding the substitution then gives a unique maximal term whose coefficient is its original nonzero coefficient. This explanation is confined to this report, not put inside the new node's statement.

## Review by Q85

I checked the item against Tag 051P and the new helper against Tag 051N (`lemma-helper-polynomial`, algebra.tex lines 27963–27994), including its cited finite-support weight lemma 051M. The helper allows arbitrary commutative rings, including rings with zero divisors; the unique maximal weighted term has its original nonzero coefficient, so it cannot be cancelled by another monomial. For n=1 there are no substitutions and the leading coefficient is already an original nonzero coefficient. In the zero ring there is no nonconstant polynomial, so the hypotheses cannot hold. Nonconstant polynomials such as 2x over Z/4Z show why the helper's coefficient must only be nonzero, rather than a unit. The field hypothesis is used only when applying it to the item and rescaling by that coefficient.

I opened the statement of every cited node and checked the uses as follows.

1. `def-weil-pbc-localization-at-prime` supplies exactly R_p and its residue quotient; the two explicit fraction formulas prove the identification with Frac(R/p). `def-kun-transcendence-degree` says a transcendence basis computes the degree; the variables themselves form one at the zero prime because no polynomial relation vanishes and every rational function is generated by them. `def-weil-pbc-mv-polynomial-ring` supplies the coefficient description and variable maps. `def-weil-finitely-generated-module` makes the rank-one generation of an isomorphism its finiteness. These are direct definition checks, not an appeal to the unproved normalization theorem. Induction is on n and includes the extra bound r<=n, so it also proves that the cardinal r here is finite. For n=0 the only prime is zero and the identity map works.

2. The new helper supplies a positive-degree leading term with nonzero scalar coefficient. I checked that a nonzero polynomial in a proper prime over a field cannot be constant. The inverse of the triangular substitution is written with a minus sign, verified generator by generator using the polynomial universal property. The prime is transported as sigma(q), not silently kept fixed; the fraction formula identifies its residue field over k. The rescaling is legal over a field. These details repair the potentially ambiguous coordinate replacement in the source.

3. `lem-weil-pbc-finite-of-integral-generators` states exactly that finitely many integral algebra generators give module finiteness. Here there is one generator, x_n, since all the other variables already lie in the image. Its displayed polynomial is monic with the term -y_n in the coefficient ring C, and it evaluates to zero. The step also gives the actual finite list of powers by degree reduction. No injectivity of psi is assumed or needed.

4. The statement of `def-weil-pbc-mv-polynomial-ring` supplies polynomial coefficients. Expanding H as its y_n-constant term plus y_n times a polynomial proves both inclusions in Q=pC+(y_n), not merely one. Inverse images of proper primes are prime by the product test; all ring maps are unital. This is an elementary step, with no separate ideal-correspondence theorem hidden in it.

5. `lem-weil-pbc-fraction-field-lift` applies to the injective map B/p -> E; injectivity follows exactly from p being the contraction. It embeds F into E. `lem-weil-pbc-finite-of-integral-generators` applies to the single monic algebraic generator xi of D=F[xi]. `lem-weil-pbc-finite-dimensional-domain-is-field` states the field conclusion for a finite-dimensional domain over a field; D is a domain because it is a subring of E. The step explains equality D=E: D is already a field containing A/q*, so contains all its fractions. It does not confuse the prime of C with the prime of B, and it uses no unjustified finiteness of a local ring.

6. `lem-kun-transcendence-degree-tower` states both the cardinal tower equality and that algebraic extensions have degree zero. The dependence of 1,z,...,z^N in a finite-dimensional vector space explicitly supplies algebraicity for every z, satisfying the node's hypothesis. The field embeddings fix k, including the sigma residue isomorphism, so this is equality of degrees over the same k. This identifies the induction parameter for p with the original r.

7. The induction hypothesis applies to the genuine prime p of the (n-1)-variable ring over the same field, and the strengthened hypothesis gives r<=n-1. Extending beta by the last variable uses only the polynomial universal property. The coefficient-by-coefficient expression with the same finite module generators proves finiteness of that extension directly, using `def-weil-finitely-generated-module`. There is no uncited general base-change theorem in this step.

8. Evaluation at z_n=0 and the explicit contraction from step 4 give an equivalence of ideal memberships. The argument uses beta^{-1}(p) from the induction hypothesis and subtracts the constant term; both directions are written. This proves the required coordinate ideal, including r=0 and r=n-1, when respectively all coordinates or only the last coordinate occur. The only cited node is the polynomial definition providing the coefficient expansion.

9. `lem-weil-pbc-finite-module-over-finite-algebra` states finiteness under restriction of scalars with explicit products of generators, and applies twice with the final ring as its own module. I used this unmerged Mathlib leaf, rather than the merged synonym `lem-weil-pbc-finite-ring-map-transitive`. The rank-one finiteness of sigma^{-1} is exhibited. The inverse-image calculation uses sigma(q)=q*, with the correct orientation. Composing sigma instead would generally give the wrong prime. All maps remain k-linear on constants, and renaming the input variables preserves the ideal formula.

I tested the induction on q=0 in every dimension, n=0, a nonzero irreducible prime in k[x], a maximal prime (including inseparable residue fields), and q=(x_2) in k[x_1,x_2]. A non-coordinate relation such as x_1x_2-1 requires the nontrivial shear and is handled by the same positive-degree monic construction. No infinite-field or separability hypothesis is used. Each non-elementary step is below 2000 characters; none hides an additional comparison or a lemma called standard. The two longer elementary computations are the zero-prime/base case and the coefficient proof of polynomial-extension finiteness; both arguments are written explicitly. I checked B1–B9, C1–C8, D1–D5 and E1–E7 against the files: one new statement-only helper, no new definitions, exact source tags, no duplicated existing statement, no moved clause of the item, and no unproved fact used beyond the cited generic nodes and the displayed elementary arguments. All proof dependencies are the union of the uses lists, and the citations file copies the actual statements without paraphrase.
