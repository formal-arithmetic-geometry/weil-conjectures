1. Files written:
- `dag/nodes/sec-six-functors-basics/lem-sfb-cocharacter-limit-smooth-structure.json` (item; split into seven proof steps).
- `dag/nodes/sec-six-functors-basics/lem-sfb-smooth-affine-concentrator.json` (statement-only supporting node; Mathlib searches found no match).
- `dag/nodes/sec-six-functors-basics/lem-sfb-transverse-subgroup-product-open.json` (statement-only supporting node; Mathlib searches found no match).
- `citations.json` (verbatim citation evidence for every non-elementary use).

2. Attachments: none. Searches by the blueprint tag and by cocharacter/one-parameter/attracting terminology in the project source `lean/WeilConjectures/` found no declaration stating the item; no attachment is claimed.

3. WANTED: none. Milne, *Algebraic Groups* (2017), is present at `literature/milne-algebraic-groups_iAG2017.pdf` and pages 261--266 and 283 were read.

4. The imported node had the correct mathematical statement but no proof. I retained its hypotheses and all test-algebra clauses. The split follows Milne’s Theorem 13.33: matrix weight coordinates establish the three functors; the concentrator and fixed-scheme inputs establish smoothness; evaluation at zero gives the semidirect product; dual numbers give tangent weights; the block calculation gives unipotence; and the opposite cocharacter big cell gives connectedness. The proof uses two new, strictly smaller statement-only nodes for smooth concentrators and transverse subgroup multiplication. The two generic regularity/integrality nodes are existing tools. The item’s imported blueprint ancestor is absent (`blueprint.from.node` is null), so the new nodes preserve that nearest-ancestor value and identify their exact supporting places in the imported proof route.

## Review by Q11

I read the item source and Milne’s Definition 13.21, Propositions 13.23--13.24, Propositions 13.28--13.30, Theorem 13.33 (especially the GL(V) calculation and equations (87)--(89)), and Example 14.13. I checked the matrix convention against the definition: an entry of weight (m_i-m_j) extends over (A[t]) exactly when it has nonnegative exponent, the zero limit kills the zero-weight diagonal blocks, and the centralizer kills every nonzero-weight entry. I checked this over arbitrary commutative algebras, including nilpotents, by coefficient comparison in Laurent polynomials.

Step 1 uses the existing faithful matrix realization and integer weight-basis statements, and those statements explicitly provide a closed immersion and a finite integer-character decomposition. Step 2 uses the new concentrator node for representability and smoothness and the existing torus fixed-scheme smoothness node for (Z_\lambda); I verified that both applications have smooth ambient and invariant closed subschemes. Step 3 is the explicit evaluation-at-zero homomorphism and inverse formula, so its semidirect multiplication formula is a direct calculation. Step 4 uses the weight-basis statement on the Lie representation and checks the three tangent conditions with (F[\epsilon]/(\epsilon^2)), including the reversal for (-\lambda). Step 5 is the strict upper-triangular block calculation and directly matches the stated definition of unipotence. Step 6 checks (U_{-\lambda}\cap P_\lambda=1) on every test algebra and the direct-sum tangent condition before applying the new transverse-product node. Step 7 uses the existing smooth-to-regularity and regular-connected-integral nodes; the big cell is nonempty open in the integral (G), and the explicit sections of the two projections transfer connectedness to (P_\lambda,Z_\lambda,U_\lambda). I checked every citation quote against the cited node’s statement in `citations.json`, and tested edge cases in the proof text: the zero cocharacter has only weight zero, gives (P=Z=G,U=1); and the one-dimensional representation gives the expected triangular/block descriptions.

## Not duplicates

lem-sfb-smooth-affine-concentrator vs lem-sfb-projective-attracting-cells: the new statement concerns a general affine smooth scheme and an arbitrary smooth invariant closed subscheme, whereas the existing statement assumes a smooth connected projective scheme with isolated fixed points and concludes affine-space strata. Neither hypothesis package specializes to the other.

lem-sfb-smooth-affine-concentrator vs lem-sfb-torus-fixed-scheme-smooth: the existing result concerns only fixed points; the new functor consists of points whose orbit has a limit in an invariant closed subscheme, which may have nonconstant orbits.

lem-sfb-transverse-subgroup-product-open vs lem-sfb-smooth-subgroup-tangent-generation: the existing result says that a closed subgroup containing a spanning family equals the ambient connected group. The new result proves that the multiplication morphism of two transverse subgroups is an open immersion without assuming connectedness; generation alone gives neither an immersion nor a product chart.

lem-sfb-smooth-affine-concentrator vs lem-sfb-cocharacter-limit-smooth-structure: the geometric input has no group-structure, Lie-weight, semidirect-product, unipotence or connectedness conclusion. The item still derives its subgroup laws and all those conclusions in its own proof.

lem-sfb-transverse-subgroup-product-open vs lem-sfb-cocharacter-limit-smooth-structure: the input concerns arbitrary smooth transverse subgroup pairs, with no cocharacter or limit functor. The item proves transversality and uses the resulting open set only in its connectedness argument.

The whole imported blueprint was searched for cocharacters, concentrators, weight decompositions and subgroup multiplication. No equivalent blueprint statement was found. The whole DAG statement search found the above related inputs, which were read before deciding to create the two new nodes. No new source uses a Stacks tag also carried by another node: the new sources are the specific Milne results read locally.

## Source error

Milne's printed p.266 has two evident slips in the proof: the identity diagonal condition for the matrix group U is written with diagonal entries zero, and the displayed limit-map domain is printed as G although the limit exists on P. The split uses diagonal entries one and the domain P, as forced by the definitions and Example 13.31. These are corrections to the source's proof notation; the item's mathematical statement is unchanged.

## Edge cases and source checks for the supporting nodes

For the smooth-concentrator node I read Definition 13.21 and the proofs of Propositions 13.23--13.24, including the graded-local proof of 13.22 through Lemmas 13.25--13.27. This is a genuine geometric input, not an elementary inference from smoothness. A trivial action gives X(Z)=Z; empty Z gives the empty smooth scheme; for A^1 with weight +1 and Z={0}, the concentrator is A^1; for weight -1 it is {0}. These tests also verify the direction of the weights and the allowance of nilpotents in the test algebra.

For the transverse-product node I read the argument for Theorem 13.33(d) at p.266. Its hypotheses concern the scheme-theoretic intersection, not merely k-points; this rules out infinitesimal intersections in positive characteristic. Neither connectedness nor reductivity is used. The complementary triangular subgroups in GL_n provide the motivating case; H=1 and K=G gives the identity open immersion, and a disconnected G is allowed because the image need not be all of G. The non-elementary passage from a trivial stabilizer and invertible tangent map to an open orbit is entirely the new node's conclusion, not an unrecorded claim in the item's proof.

All item proof steps are shorter than 2000 characters. The new nodes have empty proof arrays and no proof dependencies; their future arguments are not smuggled into their statements.

5. Nothing remains unfinished in this split. The two new nodes are intentionally statement-only and enter the stage-1 queue for later splitting.
