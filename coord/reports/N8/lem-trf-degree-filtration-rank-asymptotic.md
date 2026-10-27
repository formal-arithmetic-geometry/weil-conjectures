# Stage-1 delivery: lem-trf-degree-filtration-rank-asymptotic

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-degree-filtration-rank-asymptotic.json`: statement unchanged; eight-step split of BGR 5.3.3/4.
- `dag/nodes/sec-trace-formula/lem-trf-degree-valuation-orthogonal-basis.json`: statement, unsplit; no Mathlib match. Total-degree absolute value and orthogonal spectral bases of arbitrary finite field extensions.
- `dag/nodes/sec-trace-formula/lem-trf-product-minpoly-spectral-maximum.json`: statement, unsplit; no Mathlib match. Generic minimal-polynomial spectral maximum formula for finite products of finite field extensions.
- `citations.json`: twelve citations, quoting the full verbatim statements read for the corresponding steps.

Two new nodes, zero new Mathlib leaves. The source scan, three page images, search log and preparation script are sandbox research material, not DAG delivery files.

## Attachments

None for the item. Searches of `lean/WeilConjectures/` for the exact blueprint tag, degree-filtration/rank-asymptotic phrases, total-degree spectral norms and orthogonal spectral bases found no declaration giving this item or either new lemma. The unrelated filtration and cohomology hits do not concern this algebraic degree filtration.

I reused the existing node `lem-weil-pbc-finite-type-field-integral-closure-finite`, whose project declaration is `Algebra.FiniteType.finite_integralClosure` in `WeilConjectures/Mathlib/RingTheory/DedekindDomain/IntegralClosure.lean:299`. Its hypotheses include arbitrary finite extensions, without separability. This is an existing recorded declaration, not a new attachment claim for this delivery.

## Wanted sources

WANTED: Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*, Proposition 5.3.3/1 and Lemma 5.3.3/4, printed pp.214 and 216–218 (scan PDF pp.220 and 222–224), for the item and both new nodes. There is no archival copy at the source path under `literature/`. I downloaded the primary scan cited by the live item into the sandbox and read the page images directly: the scanned PDF has no extractable text on these pages. The mathematical source was therefore actually read, while the missing project archival copy remains WANTED. The proof is marked agent-written following the source, and no project literature file was written.

## Problems and corrections

The live item had no proof and no sandbox attempt existed. Its statement agrees with the source. No STATEMENT-DISPUTED correction is necessary. In particular, the finite algebra is reduced but need not be a field, and field factors need not be separable. I did not replace the spectral norm by a multiplicative extension norm; that replacement is unjustified for this incomplete base.

The source says to choose integral basis vectors and an orthogonal basis whose polynomial span contains the normalization. I expanded both denominator clearings explicitly. They go in opposite directions: multiply the initial basis vectors to make them integral; divide an orthogonal basis by a common denominator of the normalization generators' coordinates to make its polynomial span contain the normalization. Orthogonality survives this common rescaling by scalar homogeneity. The final asymptotic is given as a finite product of factors tending to one, rather than an unsupported claim about Hilbert polynomials.

The latest blueprint unit and ancestor were read. This inherited analytic branch is historical auxiliary support for normalization; the current unit uses contracting correspondences. I preserved the inherited blueprint ancestor and via list and did not replace a unit step. The algebraic normalization lemma is declared as a generic tool use in `split_report.tool_uses`.

## Search record

All Mathlib searches newly recorded in this delivery were run through the required `msearch.py N8 lem-trf-degree-filtration-rank-asymptotic` command and read. Their actual tool/query/digest summaries are retained in `searches.jsonl`; each new node records its own five searches, including a second semantic phrasing. The item records five new searches as well as preserving all of its imported searches.

For the item, `IsIntegralClosure.rank` is about module rank, and `Polynomial.hilbertPoly` does not identify the spectral filtration. `Polynomial.integralNormalization_degree` concerns a polynomial operation, not normalization of an algebra. For the orthogonal-basis node, the norm axioms and complete-base theorems give no such basis over the incomplete field; the valuation on a function field also does not give it. For the product node, `Pi.spectrum_eq` is about the algebraic spectrum over the base, which need not split these polynomials. `max_norm_root_eq_spectralValue` assumes a split polynomial in a normed field and still needs a product-minimal-polynomial comparison. Neither result is a one-line specialization of the new product statement. I read `SpectralNorm.lean` around the coefficient definition, root comparison, field hypotheses and spectral algebra norm, and the recorded finite-normalization project declaration.

Whole-DAG searches included total degree, orthogonal bases, finite reduced products, finite normalization and spectral products. Blueprint searches included degree filtration, spectral norm, orthogonal, monomials, total degree and spectral norm on a product. The hits concerned unrelated cohomological filtrations, Hilbert polynomials, or character orthogonality. Existing Artinian decomposition and finite-normalization statements were reused instead of duplicated.

## Not duplicates

lem-trf-degree-valuation-orthogonal-basis vs lem-trf-gauss-spectral-coefficient-cartesian: the new statement uses the total-degree valuation on the rational function field and an orthogonal basis over that field; the existing statement uses a Gauss valuation and bases of finite-dimensional subspaces over the constant field, which is additionally complete and stable.

lem-trf-degree-valuation-orthogonal-basis vs lem-trf-incomplete-spectral-algebra-norm: norm axioms do not assert existence of orthogonal bases; the new node is the special stability theorem for the total-degree valued rational function field.

lem-trf-product-minpoly-spectral-maximum vs lem-trf-weak-spectral-completion-product: the existing node constructs a completion over a complete base under a coordinate-norm equivalence hypothesis. The new node compares minimal-polynomial coefficient radii in a finite product over any valued base, without completion or that equivalence hypothesis.

lem-trf-product-minpoly-spectral-maximum vs lem-trf-degree-filtration-rank-asymptotic: the new node contains no integral closure, filtration, dimension count or limit. It is a generic spectral-polynomial identity needed for the source's reduction to field factors, not a restatement of the item's growth conclusion.

## Review by N8

I read the statement of BGR Lemma 5.3.3/4 on printed p.216 and its entire proof on pp.217–218. I also read Proposition 5.3.3/1 on p.214: it explicitly asserts stability for the total-degree valuation and uses discreteness together with weak stability; its application on p.217 supplies the orthogonal-basis input. For the product node I read the first paragraph of the proof on p.217, where the spectral maximum formula is explicitly given. Both new nodes carry only statements, with complete hypotheses and definitions, and their proof arrays and proof-dependency arrays are empty.

Step 1 uses exactly the finite-dimensional-algebra Artinian theorem and the reduced Artinian canonical residue-product theorem. I opened both node files: the former applies to a finite-dimensional commutative algebra over any field, the latter requires precisely the reduced and Artinian hypotheses available here. The field quotients are finite-dimensional because images of a basis span. The index set is nonempty because the item excludes the zero algebra. I also read Stacks algebra.tex, Tags 00J6, 00J7 and 00JB, and their labels.

Step 2 uses the new product identity exactly as stated and the existing incomplete spectral algebra norm node exactly for the ultrametric and scalar-homogeneity identities on field factors. That existing node does not claim a product algebra is a field; the new node is what bridges to the product. The integral-closure definition node explicitly says the integral elements form a subring containing the base; applying monic equations coordinatewise and multiplying the finitely many monic annihilators proves the two directions of the closure comparison. It follows that the filtration is an F-linear space. I checked that the algebra isomorphism preserves annihilating polynomials and hence the coefficient formula.

Step 3 uses only the integral-element definition, and explicitly turns each rational monic relation into a monic polynomial over A after multiplication of the element by a denominator. The scaled vectors are still a Q-basis. A finite family of real spectral norms admits the required nonnegative integer exponential bound.

Step 4 uses the exact monomial description in the polynomial-ring definition, the subalgebra clause in the integral-closure definition, and the field norm node's ultrametric and scalar identities. Its injectivity follows by grouping monomials by the Q-basis vectors. The image bound is written explicitly. This is elementary finite-dimensional linear algebra after those statements, rather than a hidden lower-growth lemma.

Step 5 uses the finite-type-domain normalization node with A the n-variable polynomial ring, Q its fraction field and L an arbitrary finite extension. I checked its complete statement and Stacks Tag 0335, proposition-ubiquity-nagata, specifically the field and finite-type cases. No separability, perfection, or finite-type assumption on the normalization itself is introduced. The new orthogonal-basis statement applies to exactly the total-degree valuation in force. I wrote the common-denominator containment and rescaling equality; these are direct coordinates and scalar homogeneity, not a new lemma hidden in a long step.

Step 6 uses only the containment and orthogonality already obtained in step 5 and takes logarithms of an explicit positive exponential inequality for each nonzero polynomial coefficient. Zero coefficients require no degree convention. The coordinate injection proves finite-dimensionality for every nu, including nu=0. This is the explicit upper dimension estimate, not an appeal to a separate clause of the item.

Step 7 proves its monomial count by an explicit reversible stars-and-bars map, and proves the shifted-binomial limit as a finite product. The elementary finite-dimensional dimension inequalities and real finite-product/squeeze rules require no new algebraic input. Step 8 sums finitely many field-case limits; dimension additivity follows by taking the union of the component bases. Neither step introduces a new supporting theorem under the name of the item's own clause.

I checked small cases: for M=Q, B(nu) is exactly the polynomials of degree at most nu, with dimension binomial(nu+n,n). For M=Q×Q, its spectral radius is max of the two coordinates even when the two coordinate minimal polynomials coincide, so the dimension is twice that number. In characteristic p, L=F(t) with X=t^p has D=F[t], s(t)=exp(1/p), and dimension p nu+1 in one variable; its normalized limit is p, the full inseparable degree. For the product node, x=0 has minimal polynomial Z and spectral value zero; repeated coordinate polynomials do not multiply their radius. The singleton product case is the identity. The orthogonal statement in this inseparable example is realized by 1,t,...,t^(p-1), since their norm exponents are distinct modulo the integer value group. These checks preserve all original hypotheses.

I checked delivery-errors B–E against the actual files. Every non-elementary fact used is named by a cited statement; the two new facts are genuine inputs rather than elementary coordinate estimates or clauses of the growth formula. Every citation quote in citations.json is verbatim from its node statement. No proof step exceeds 2000 characters. No source from the forbidden SGA route is used. Nothing was written to the shared repository or the launcher, and no compiler or Lake tool was run.

## Unfinished work

The two new supporting statements remain unsplit as required by a one-level stage-1 split. No part of the item's proof is left as an unspecified argument.
