# Stage-1 delivery: lem-sfb-abelian-degree-polynomial

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-degree-polynomial.json: item, split; statement unchanged.
- lem-sfb-top-intersection-multilinear: statement, unsplit; no Mathlib match.
- lem-sfb-top-intersection-pullback: statement, unsplit; no Mathlib match.
- lem-sfb-equal-dimension-isogeny-criterion: statement, unsplit; no Mathlib match.
- lem-sfb-bounded-line-polynomial-interpolation: statement, unsplit; no Mathlib match.
- lem-sfb-rational-tensor-fractions: statement, Mathlib leaf; localization instance and its surjectivity/equality interface.

All node files are in dag/nodes/sec-six-functors-basics/. citations.json quotes the actual statement of every node in each proof step. searches.jsonl is the original msearch log; the records in new nodes use exactly its queries.

## Attachments

None. Searched the project WeilConjectures/ by the item tag, isogeny, abelian variety, endomorphism and degree-polynomial language. Read AbelianVariety/Cube.lean, Projective.lean and the degree portions of Isogeny.lean. They supply supporting geometry, but no declaration states polynomiality of endomorphism degree on rational spans. An elliptic division-polynomial degree or linear-map characteristic-polynomial result is not an attachment to this item.

## WANTED

None. Milne AV and the Stacks sources used here are present.

## What was wrong or incomplete

The item had no proof; its statement is correct and is retained, including positive dimension and allowance for the zero restriction. The nearest blueprint ancestor command prints None for this inherited auxiliary chain; its existing blueprint.from.node is null. I retained that provenance and the existing via chain, adding the item to each new node's via and specifying the exact local source place. The latest blueprint main is 7284bb09daf97437d544c51882b325f9c52cd345; I read its direct-images proof (3) and stability unit. No chapter or unit route is changed.

Milne Lemma 10.12 is printed without a uniform degree bound. Its displayed induction chooses a fixed degree for all values of the other coordinates, which its bare hypothesis does not supply. I do not use that unbounded version. Proposition 10.13 supplies the uniform bound 2g, and the new bounded interpolation node states exactly the valid lemma needed. There is no dispute with the item's statement. The item proof additionally spells out the polynomial identity comparing Q_(a,mb)(mT) and m^(2g)Q_(a,b)(T), so the assertion on integer points is not silently identified with the assertion on all rational points.

## Not duplicates

lem-sfb-top-intersection-multilinear vs def-sc-intersection-number: the latter defines the coefficient of an Euler-characteristic polynomial; it does not state tensor additivity, which is the theorem of Tag 0BER. Both cite 0BEP because it fixes the intersection convention.

lem-sfb-top-intersection-pullback vs lem-sc-deg-pullback-finite: the existing lemma assumes a finite surjective morphism and an ample module and uses Hilbert degree; the new lemma covers arbitrary morphisms of equal-dimensional proper integral varieties, including zero intersection for nondominant maps and nonample line bundles. That zero clause is indispensable in step 1.

lem-sfb-equal-dimension-isogeny-criterion vs lem-sfb-finite-kernel-equal-dimension-isogeny: the existing node starts with finite kernel over an algebraically closed field and concludes surjectivity; the new node starts with surjectivity over any field and concludes isogeny. Neither that node nor lem-sfb-equal-dimension-abelian-retract supplies this direction.

lem-sfb-rational-tensor-fractions vs lem-trf-torsionfree-rationalization-injective: the existing node assumes torsion-freeness and asserts injectivity; the new Mathlib leaf asserts denominator existence and the equality-up-to-positive-multiple criterion without that assumption. It does not require finite generation of End(A), which would be circular here.

lem-sfb-bounded-line-polynomial-interpolation vs lem-sfb-abelian-degree-polynomial: the new statement is a general interpolation lemma about an arbitrary function satisfying an explicit uniform line-degree hypothesis; it has no abelian variety, degree function, rationalization construction or homogeneity conclusion. The item proves the uniform line-degree hypothesis using geometry, rather than moving its conclusion into the new node.

Searched all DAG statements and source places for cube, intersection numbers, 0BER, 0BET, Proposition 7.1, Lemma 10.12, tensorProduct_isLocalizedModule, bounded-degree polynomial restrictions, and rational localization. Ran blueprint_refs.py searches for degree polynomial, theorem of the cube, multilinear, intersection number(s), numerical polynomial, polynomial function, affine line, equal dimension, surjective homomorphism, bounded degree, positive integers, rationalization and tensor localization. Existing cube, multiplication, positivity, projectivity and degree nodes are cited instead of duplicated.

## Unfinished work

No portion of the item's argument is deferred. The four new unsplit nodes deliberately contain statements only, as required for a one-level split. Their arguments belong to their future splits; the supporting source arguments are described below for review. No Lean was written or compiled, no agents were started, and no repository or launcher file was changed.

## Review by Q142

I read Milne AV Chapter I Remark 10.11, Lemma 10.12 and Proposition 10.13 (printed pp.47–48), the convention preceding Theorem 10.9 (p.46), Corollary 5.3 (p.22), and Proposition 7.1 and its proof (p.32). I also opened Stacks varieties.tex, definition-intersection-number (0BEP), lemma-intersection-number-additive (0BER), lemma-intersection-number-and-pullback (0BET) and lemma-ample-positive (0BEV). The item has the same field, abelian variety and dimension hypotheses as Milne's degree calculation. It uses no simple-variety assumption, Tate-module faithfulness, finite generation of End(A), or SGA source.

Step 1 uses the statements of lem-sc-abelian-variety-projective and lem-sc-ample-tensor to construct an ample symmetric module, and lem-sc-abelian-variety-characterization for integrality. I checked those statements over any field, not just an algebraically closed one. def-sc-intersection-number and def-sc-hilbert-degree give the two coefficient conventions; expanding p(n1+...+ng) identifies their self-intersection values. lem-sc-positive-ample-hilbert-degree then supplies strict positivity. The new criterion supplies exactly nonisogeny implies nondominant; the new pullback node includes exactly the zero case as well as the dominant function-field factor. lem-sc-isogeny-degree identifies that factor with kernel order in the isogeny case. The finite-surjective-only pullback node would not suffice for the nonisogeny case and is therefore not used as if it did.

Step 2 takes the symmetric-module multiplication pullback from lem-sc-mult-n-pullback and tensor additivity from the new multilinearity node. The factor is n^(2g), because there are g entries each scaled by n². Negative integers use symmetry, not a positive-integer result applied outside its hypotheses; zero uses g>0 and the constant map's trivial pullback.

Step 3 takes only the denominator and equality clauses explicitly stated by lem-sfb-rational-tensor-fractions. Its clearing argument uses cma=cnb, not an unproved injection of End(A) into its rationalization. The equality of normalized degree values follows by cancelling positive rational powers. Hence there is no circular appeal to the parent finite-free Hom theorem.

Step 4 uses the actual seven-term statement of thm-sc-theorem-of-cube, pulled back along (na+b,a,a). Cancelling the two equal a terms gives C_(n+2)-2C_(n+1)+C_n=(2a)*N-2a*N, with the signs checked against Milne's displayed formula. def-sc-invertible-module supplies the tensor inverses. The forward and backward induction is written out; negative integers are included.

Step 5 uses the multilinear statement to expand a g-fold product of quadratic classes. The maximal degree is 2g even when some coefficients vanish. The rational-tensor leaf supplies common denominators for v and w. I checked the rescaling identity at integer j first, then polynomial uniqueness, then t=p/m. This avoids inferring rational-line polynomiality merely from agreement on integers. Each division is by the strictly positive c or a positive integer.

Step 6 applies the bounded interpolation statement with the uniform bound just proved. For its supporting lemma I checked the bounded variant of Milne's induction: choose D+1 distinct field elements once; interpolate in the last coordinate. Each coefficient is a fixed linear combination of the functions with the last coordinate specialized to those elements, so induction gives a polynomial in all other coordinates. Once a finite multivariate polynomial exists, restricting it to tv shows every homogeneous component of degree greater than D vanishes on K^r, hence is zero by repeated one-variable root bounds. The same repeated root bound gives the stated determination by values. This is valid over any infinite field and also for r=0 and D=0. The Mathlib hits MvPolynomial.funext and Lagrange.interpolate_poly_eq_self are supporting operations, not a one-line specialization proving this entire interpolation statement.

Step 7 uses only the determination-by-values clause and the previously proved scaling law to compare coefficients of t^|nu|X^nu. No nonzero homogeneous monomial of a different degree survives. The finite-kernel order in def-sc-isogeny is positive because the kernel contains the identity section. I checked V=0 (the polynomial is zero), a=0, a nonisogeny projection on a product of elliptic curves (top intersection zero), and a=[n] (degree n^(2g)). Positive characteristic is allowed: inseparable isogenies use scheme-theoretic degree, never geometric kernel-point cardinality.

For the five new statements I checked all objects are introduced, every specialized notion has its definition dependency, no proof is hidden inside an unsplit statement, and no node repeats the item's clauses. For the Mathlib leaf I read BaseChange.lean:98, LocalizedModule/Basic.lean:547–555 and FractionRing.lean:81. tensorProduct_isLocalizedModule with S=positive integers gives the localization instance; its surj and eq_iff_exists interfaces give the two clauses after TensorProduct.comm. Each declaration is recorded with its file and line. The other searches returned ordinary multilinear maps, cover intersections, division polynomials, finite-dimensional linear algebra and polynomial restrictions, none of which supplies the claimed geometry.

The generic abelian-variety tools from other units are explicitly declared in split_report.tool_uses. All seven proof steps are under 2000 characters. I corrected the omitted bounded-interpolation hypothesis and the integer-to-rational compatibility gap before delivery; the item's statement and all inherited provenance are preserved.
