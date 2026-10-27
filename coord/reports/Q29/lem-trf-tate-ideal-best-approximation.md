## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tate-ideal-best-approximation.json`: item, statement unchanged, split into three proof steps.
- `dag/nodes/sec-trace-formula/lem-trf-exponent-tuples-wqo.json`: statement, Mathlib leaf `wellQuasiOrdered_le`, specialized using `Pi.wellQuasiOrderedLE`.
- `dag/nodes/sec-trace-formula/lem-trf-tate-convergent-division.json`: statement, no Mathlib match, unsplit analytic division input.
- `citations.json`: every step/cited-node pair, quoted verbatim from the statement read.

## Attachments

None. Searches of `lean/WeilConjectures/` for the item id, Tate algebra, best approximation, strictly closed, Grauert, restricted-series division, and the proposed auxiliaries found no declaration stating the item or either new node. The two Koszul occurrences of “Tate algebra” refer to graded commutative resolutions, not analytic restricted series.

## WANTED

WANTED: Bosch–Güntzer–Remmert, Non-Archimedean Analysis, Corollary 5.2.7/8 and surrounding division arguments, for `lem-trf-tate-ideal-best-approximation` and `lem-trf-tate-convergent-division`. The book is absent from this checkout; its printed proof has not been read.

WANTED: archival local copy of Siegfried Bosch, Lectures on Formal and Rigid Geometry, April 2008, §1.3, for this item. I read the online text at https://www.uni-muenster.de/IVV5WS/WebHop/user/weckerm/heft378.pdf, printed pp.19–21 (PDF pages 20–22). Corollary 9 states exactly the item's best-approximation assertion. Its proof uses an orthonormal basis adapted to the ideal, supplied in the proof of Corollary 7 with Theorem 6's coefficient-subring hypothesis. I have not treated an arbitrary lifted residue basis as a Banach basis without that hypothesis. The present proof is an independently written finite-division argument, and `proof_origin.by` is `agent`.

## Problems found and changes

The imported node was a statement-only analytic input; it had no argument to audit. Its statement is correct and remains verbatim. In particular, closedness of an ideal alone would not establish norm attainment in a general Banach space. The split provides the stronger analytic ingredient needed rather than citing closedness or an epsilon-approximation theorem.

I read the current blueprint in `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.md`, the chapter and unit records, and SETUP's three-level rule. This item belongs to a historical analytic normalization chain below the node level; the current unit is about contracting correspondences. The delivery changes neither the unit nor the chapter nor the current proof of contracting local terms. Blueprint provenance and the full via-chain are retained, and the new nodes add this item to their via-chain. Searches with `tools/blueprint_refs.py search` for Tate, Gauss, Dickson, division, convergent division and well-quasi, together with searches of the statements throughout `dag/nodes/`, found no duplicate of either auxiliary. In particular the formal-coefficient division nodes concern characteristic-zero formal rings and additional Hilbert/Jacobian conditions; they do not supply finite-list analytic division over an arbitrary complete nonarchimedean field.

## Argument retained for the unsplit division node

This paragraph is a plan for the next worker, not a proof inserted into the statement-only node. It also checks that the analytic input is independently valid and does not assume the item.

Given finitely many norm-one series b_i, let H_i be the polynomial consisting of exactly their coefficients of modulus one, and let e_i=b_i-H_i. The H_i have the same graded-lex leading exponents as b_i and unit-modulus leading coefficients; restrictedness implies c=max_i ||e_i||<1 (empty list separately). Ordinary multivariate polynomial division can be performed over the valuation ring with unit leading coefficients. More explicitly, recursively reduce each monomial by the first divisor whose leading monomial divides it; all replacement monomials have strictly smaller graded-lex exponent and all replacement coefficients have modulus at most one. If no divisor applies, move that monomial to the remainder. Thus the algorithm on basis monomials defines K-linear maps Q_i and R on polynomials, with Gauss operator norms at most one. R's image is supported away from all multiples of L(H_i), and x=sum Q_i(x)H_i+R(x). This requires neither a Gröbner basis nor uniqueness of the remainder for the generated ideal.

Polynomials are dense in the Tate algebra; coefficientwise completeness and the cofinite-null condition make it the completion for the Gauss norm. The bounded maps therefore extend to it. Multiplication by each fixed restricted series is bounded, since the ultrametric coefficient-convolution inequality gives ||uv||≤||u||||v||. Put E(x)=sum Q_i(x)(H_i-b_i), so ||E(x)||≤c||x|| and x=sum Q_i(x)b_i+R(x)+E(x). For x_n=E^n(f), the series q_i=sum_n Q_i(x_n) and r=sum_n R(x_n) converge because their nth summands have norms at most c^n||f||. Summing the preceding identity gives f=sum q_i b_i+r, with all stated norm bounds. Each excluded coefficient of R(x_n) is zero, hence its coefficient in r is zero too. This proves precisely the new node, without assuming any ideal is closed or has best approximations. The finitely many tails have a uniform c<1 even when the value group is dense; no discrete valuation or spherical completeness is hidden in the argument.

## Not duplicates

lem-trf-tate-convergent-division vs lem-trf-tate-ideal-best-approximation: finite-list division is about arbitrary chosen norm-one divisors and gives a supported remainder; it makes no assertion that the remainder minimizes distance to an arbitrary ideal. The item's finite leading-exponent construction and cancellation argument provide that conclusion.

lem-trf-tate-convergent-division vs lem-trf-formal-coefficient-transform-criterion: the latter concerns formal characteristic-zero Taylor ideals satisfying special division/Jacobian data, not Gauss-bounded division of restricted series over any complete nonarchimedean field.

lem-trf-exponent-tuples-wqo vs lem-sfb-bounded-homogeneous-groebner-degree: the latter bounds degrees of homogeneous polynomial Gröbner bases; the new leaf is the exact sequence-pair property on tuples, with no polynomials, fields or degree bound.

No Stacks tag is claimed for either analytic statement. These sources are not Stacks results; inventing a tag would obscure the actual analytic input. The Mathlib leaf cites the source declarations and the lines read.

## Review by Q29

I checked the item against Bosch §1.3 Corollary 9 online and against its existing statement; no hypothesis is added or dropped. I read every cited node statement, including both newly written auxiliaries, in full. I also read the existing field and restricted-series definition nodes: they supply exactly the field and the cofinite-null restricted-series ring that the item and division node use. The item states its absolute-value and completeness assumptions explicitly; no discrete-value-group, algebraic-closedness, quotient-reducedness or ideal-closedness assumption enters.

In step 1, `lem-trf-tate-convergent-division` supplies the chosen graded-lex convention and L(u), and `lem-trf-exponent-tuples-wqo` supplies exactly an increasing pair in a sequence under the componentwise order. The finite coinitial subset is proved there by the explicit bad-sequence contradiction, not taken from a leaf that states something weaker. The coefficient-maximum observation follows immediately from the stated cofinite-null condition and a fixed nonzero coefficient. I checked the empty set D separately. This step is non-elementary because it invokes Dickson's lemma; it is not falsely marked elementary.

In step 2 the division statement's norm-one hypothesis is met by dividing each u_beta by its own leading coefficient, whose absolute value is its Gauss norm. The list is finite by step 1 and its members lie in the given ideal because it is a K-algebra ideal. The cited statement gives both the decomposition and the exclusion of every leading-monomial multiple from the remainder's entire support, not just from its maximal-norm terms. This is precisely the condition the next step uses. The new node is statement-only, fully introduces K, s, t, the norm, order, divisors, coefficients and remainder, and carries no proof or proof dependencies. Its independent contraction argument is recorded above so the missing printed BGR proof is not concealed.

Step 3 is a coefficientwise ultrametric calculation using the two preceding outputs. If ||r-k||<||r||, the coefficients of k attain ||r|| at exactly the exponents where r does, including their largest graded-lex exponent. Thus L(k)=L(r), not merely some overlapping maximal exponent. Since k lies in I, step 1 forces a divisor leading exponent below L(r), contradicting step 2. I checked that the argument also rules out a merely smaller distance even if the value group is dense and the infimum were not positive. It uses no compactness or Banach minimization theorem. The equivalence with a minimum-norm coset representative follows from the explicit representative set f-I.

I checked B–E of delivery-errors against the files and sources: new statements have independent objects and all needed notions inline or in statement dependencies; the leaf is the exact specialization, not an unproved analytic bridge; each search in the JSON was genuinely run by msearch.py and its hits read, with alternative semantic phrasings; there is no duplicate, circularity or replacement of the item by an equivalent clause. I kept the nontrivial analytic fact as an unsplit node and the elementary coefficient argument inside the item. Every cited sentence is copied verbatim into citations.json. None of the steps is over 2000 characters; their total is under 3000.

For small cases, when I=0 the list is empty, division gives r=f and g=0. When I=T_s one may use the constant one among the divisors, leaving r=0, or take g=f directly. For s=0 the ring is K and the only ideals are these two. Empty divisor lists and a constant norm-one divisor satisfy the new division lemma; for a nontrivial test, b=X-a with |a|<1 has L(b)=1, so the division remainder is constant, consistently with evaluation at a. Ideals with nonreduced quotient, such as (X^2), satisfy the same proof. The tuple leaf for s=0 gives the unique empty tuple at indices 0<1. No source error or statement dispute was found.

## Remaining work

The delivery completes this one-level split. The bounded convergent division node intentionally remains unsplit for the next worker; the tuple node is a Mathlib leaf. No Lean files were written and no compiler, Lake, library build or local forbidden preflight/check script was run. Remote mechanical checks and the final delivery result are recorded below when complete.

## Remote verification

The preliminary remote review_split passed. The first full dry run requested an explicit notion citation in the tuple leaf and a numeric mathlib_match.line; I added the existing universe/smallness convention (read in full) and line 130 of the verified declaration. This adds only the project-wide universe convention, with no change to the mathematical sequence-pair property. Citation quotes were updated accordingly.
