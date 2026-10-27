## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-curve-riemann-hurwitz-numerical.json: split the item into six steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-separable-curve-differential-nonzero.json: statement-only lemma, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-proper-curve-bundle-pullback-degree.json: statement-only lemma, unsplit; no Mathlib match.
- citations.json: verbatim statement quotations for all 12 step citations.

The sandbox initially had no item node or earlier split. I copied the live node, preserving its metadata, citations and five recorded searches. The additional searches and exact returned results are in searches.jsonl and the per-query text files. No Lean file was written and no compiler was run.

## Attachments

None. Searched the project source by the item tag and Riemann/Hurwitz, and examined nearby curve differential and divisor-degree material. No declaration states the numerical genus equality with its nonnegative remainder. Existing divisor pullback degrees address a supporting assertion, not this item or the new general proper-curve line-bundle lemma.

## WANTED

None. All sources used are available locally.

## Corrections and scope

The item is true as stated; no STATEMENT-DISPUTED correction is needed. Its source is Stacks curves.tex Tag 0C1B (curves-section-riemann-hurewitz), first paragraph and displayed calculation. I read that discussion and Tag 0C1C (curves-lemma-generically-etale), including all five equivalent conditions and the proof. The numerical conclusion only asks for an integer r >= 0, so I realize the same differential-line-bundle calculation via a nonzero section of L = Omega_X tensor (f*Omega_Y)^dual. The degree positivity is the existing lemma for nonzero sections (varieties.tex Tag 0B40, lemma-check-invertible-sheaf-trivial, proof of (5) through (1)). The split does not need an explicit different ideal or the tame formula sum(e_x-1). It neither assumes tameness nor discards wild contributions.

A real convention issue needed attention: lem-sc-canonical-degree uses divisor/Picard degree, while the degree-positivity and tensor-additivity tools use chi(L)-chi(O). Step 4 now cites the line-bundle clause of lem-sc-riemann-roch and subtracts its chi(O)=1-g clause, explicitly identifying these two degrees before using canonical degree. Merely citing the canonical divisor lemma would not justify that identification.

Both added nodes are genuine supporting assertions, not clauses of the genus formula. One concerns the differential of any dominant separable smooth curve map, with no properness or genus; the other concerns pullback of any line bundle on proper integral curves, without smoothness, separability, algebraic closure or genus. Their statements introduce every object and have no embedded proof, proof dependencies or sketches.

The nearest blueprint ancestor command returns None for this created chain; I retained the item's exact recorded place and null ancestor, and prepended the item to the existing via list for each new node. Blueprint searches were run for Riemann Hurwitz, canonical bundle, generically etale, degree of pullback, nonzero section, separable differential, degree pullback, 0AYY and 0AYZ. DAG searches checked those tags and concepts. The existing canonical-degree node is reused, not recreated. The enclosing high-genus-cover input to det-thm-sf-ctf-stability-direct-images (3) remains the route; the auxiliary curve tools are declared in split_report.tool_uses.

## Not duplicates

lem-sfb-separable-curve-differential-nonzero vs lem-sfb-curve-riemann-hurwitz-numerical: the new lemma gives nonvanishing of df from finite separability, on possibly nonproper smooth curves over any field; it says nothing about genus, degrees of line bundles or a numerical nonnegative remainder.

lem-sfb-separable-curve-differential-nonzero vs lem-a1-nonzero-differential-generically-etale: the existing statement relates nonvanishing of df to existence of an etale open, conditions (1) and (4) of 0C1C. It does not assert that finite separability of the function-field extension implies either condition. The new lemma supplies precisely (5) implies (1), and does not assume the etale open the existing statement would require.

lem-sfb-proper-curve-bundle-pullback-degree vs lem-trf-fibre-degree-ample-criterion: the existing statement is an ampleness criterion using component normalization degrees; its statement does not give the degree-scaling equality for a dominant map and arbitrary line bundle. Their source tags overlap only because the ampleness proof uses normalization degree invariance.

lem-sfb-proper-curve-bundle-pullback-degree vs lem-sc-pullback-degree: the existing statement concerns valuation-defined divisors under finite flat maps of smooth curves over algebraically closed fields. The new statement concerns Euler-characteristic degrees of invertible modules under dominant maps of arbitrary proper integral curves over any field; it includes singular curves, nonflat finite maps and arbitrary base fields. It is not a one-line specialization of the existing divisor statement.

lem-sfb-proper-curve-bundle-pullback-degree vs lem-sc-deg-pullback-finite: that existing assertion concerns Hilbert degrees of varieties relative to ample line bundles. The new assertion concerns Euler-characteristic degree of arbitrary line bundles, including ones of negative degree.

## Review by NS

I reviewed the split against delivery-errors B through E, with each cited node's statement open. For the first new node I read curves.tex Tag 0C1C, lemma-generically-etale, particularly (5) and (1): both require smooth integral one-dimensional curves, and the new node explicitly assumes dominance and the finite separable extension. For the second I read varieties.tex Tag 0AYZ, lemma-degree-pullback-map-proper-curves and its proof: it applies to nonconstant proper integral curves and all locally free sheaves. The new rank-one statement uses Euler-characteristic degree and function-field degree, and dominance rules out a constant map. Neither new statement asserts any of the item's numerical conclusion.

Step 1 is finite-dimensional linear algebra: a field extension contains a nonzero vector 1, so its finite dimension is positive. The item's induced function-field extension already asserts dominance; no separate unproved claim that every nonconstant morphism is finite is used in this step.

For Step 2 I read lem-sc-canonical-sheaf: its statement explicitly makes the differential sheaf invertible on a smooth connected curve. Integral dimension-one X and Y are nonempty connected, so it applies. I read lem-weil-pbc-invertible-pullback-tensor (1), which explicitly makes a pulled-back line bundle invertible, and the new finite-separability/nonzero-differential statement, whose hypotheses are exactly available. This does not use the proof of the preexisting generic-etaleness node to obtain its missing separability clause.

For Step 3 I read def-sc-invertible-module, including its actual definition of the dual, and def-pur-sheaf-tensor-product. The local formula for the section and its transition under two generator changes is written out; nonzero df yields a nonzero section since the local coefficient is the same. Dual and tensor local frames give a line bundle. I read lem-trf-curve-section-degree-positivity, which explicitly gives nonnegative Euler-characteristic degree for an invertible module with a nonzero section on an integral proper one-dimensional scheme. All those hypotheses hold for X, independently of whether ramification is wild.

For Step 4 I checked both clauses used from lem-sc-riemann-roch: chi(L)=deg_Pic(L)+1-g and chi(O)=1-g. I read def-pc-degree-line-bundle to check that subtracting these is exactly the other degree convention. I then read lem-sc-canonical-degree, which gives an actual canonical divisor representing Omega and its degree 2g-2. The item has the same algebraically closed base, proper smooth connected dimension-one curves and genus dim H1. This repairs the possible mismatch between the numeric invariants rather than silently identifying them.

For Step 5 I read the full statement of lem-trf-curve-degree-tensor-additive. It applies to proper schemes of dimension at most one and invertible modules, with exactly the degree used here. I wrote evaluation and its inverse in frames to justify A tensor A-dual = O. The degree definition gives deg O=0, and two applications of additivity give deg L=deg B-deg A. Isomorphism invariance follows by applying cohomology to an isomorphism; no source lemma about a different degree is substituted.

For Step 6 I reread the new pullback-degree statement: it applies to M=Omega_Y because Step 2 gave invertibility and the given map is dominant with finite function-field extension. Its equality and the previous degree computations give the result by subtraction. Every non-elementary fact used by a step is one of its cited statements; the local coefficient calculations, evaluation, positivity of finite field dimension and final arithmetic are the written elementary parts. No proof step exceeds 2000 characters or hides a standard comparison.

I tested the new nonzero-differential statement on the identity (df is identity), t mapping to t^n on the projective line with n prime to the characteristic, and t mapping to t^p-t in characteristic p (df=-dt although the degree is p). Pure Frobenius would have df=0 and is excluded exactly by separability. For the degree-pullback node I checked identity and a finite birational normalization (degree one, including a singular target), as well as O(n) under t mapping to t^d, for positive, zero and negative n. Inseparable Frobenius still scales line-bundle degree by p and is allowed in this node. For the item, identity gives r=0; t mapping to t^n on P1 gives r=2n-2; the Artin--Schreier P1 map has r=2p-2, confirming that a wild separable map of degree divisible by the characteristic is not lost. No counterexample or type failure was found.

All required Mathlib queries ran through msearch.py, including second semantic phrasings. I read the returned hits. The differential search found the field/algebra-level FormallyEtale.of_isSeparable and KaehlerDifferential.isBaseChange_of_formallyEtale; I opened their Mathlib files. They do not give a map of differential sheaves on curves without generic-stalk and localization arguments, so the geometric node is not a Mathlib leaf. differentIdeal_ne_bot concerns Dedekind-domain differents, also not this sheaf assertion. The degree searches returned polynomial, meromorphic-function or Weierstrass assertions, and no line-bundle degree formula. Queries and full outputs are retained, including original item searches; no unrun search was added.

## Unfinished work

None for this one-level stage-1 split. The two statement-only nodes intentionally remain unsplit for future workers.
