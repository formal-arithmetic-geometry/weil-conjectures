## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-standard-graded-cumulative-dimension.json: item split, statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-standard-graded-vertex-dimension.json: statement, unsplit, no Mathlib match after two semantic phrasings, LeanSearch, Loogle and source grep. One new node; zero new Mathlib leaves.
- citations.json: verbatim statement quotations for every citation of every item step.

Attachments: none. Searched WeilConjectures by the exact blueprint tag, cumulative Hilbert terminology, graded dimension, Hilbert polynomial and irrelevant-ideal dimension. Standard.lean has finite-dimensional graded pieces; LinearPair.lean:142 has Noetherianity, neither gives the item. The project HilbertPolynomial module concerns coherent Euler characteristics, not this assertion about affine standard graded algebras.

WANTED: none.

The original statement is correct, including degree zero. Its source-place summary uses a degree-piece Hilbert polynomial, but the proof of Stacks 00P6 actually passes through localization and the local Hilbert function. I followed that proof and reused its existing Hilbert–Samuel and length inputs, avoiding a second general Hilbert dimension theorem that would merely restate the item. The prior empty proof supplied no argument. No statement dispute, change of unit route, SGA source, or outstanding mathematical gap. The new input remains statement-only as required by a one-level split.

## Searches and blueprint

I ran tools/blueprint_refs.py ancestor on the item (it returns None), and searched all blueprint nodes for Hilbert, graded, irrelevant, homogeneous maximal, cumulative and 00P6. I searched the whole DAG for 00P6, lemma-dimension-graded, Hilbert-function/cumulative language, homogeneous minimal primes and localization/dimension. The existing source-labelled nodes listed below were opened; none states the vertex-localization assertion. The blueprint no longer has an imported root on this historical auxiliary chain: I retained the exact null ancestor, historical place, and complete via chain, adding this item to the new node's via. The latest blueprint directory was used. No chapter or unit was edited.

Every Mathlib query added here was executed with msearch.py and read; searches.jsonl retains the results. Searches for the vertex lemma found localization dimension equals prime height, a bound quantified over ALL maximal ideals, and unrelated graded-localization/generation results. Those do not prove that this particular maximal ideal attains global dimension. Searches for the item found polynomial-ring dimension formulas but no cumulative growth theorem for standard graded quotients. Both second semantic phrasings also failed to match. No unavailable service was represented as a negative result. Older searches in the copied item were preserved.

## Review by Q124

I read algebra.tex Tag 00P6 (lemma-dimension-graded), including its proof, not only its degree-piece statement. It first identifies dim S with dim S_m using homogeneous minimal primes and components through the vertex; only afterwards it compares Hilbert functions and invokes Tag 00KQ (proposition-dimension). I also read Tag 00JU (lemma-graded-ring-minimal-prime), Tag 00OT (lemma-dimension-at-a-point-finite-type-over-field), and the Noetherian permanence statement Tag 00FN (lemma-Noetherian-permanence). The new lemma is exactly the pre-Hilbert equality from this proof. It has no Hilbert polynomial or growth conclusion, and thus is a strictly smaller geometric input rather than a renamed version of the item. It assumes the same field, degree-zero field and finite degree-one generation conditions as 00P6. Its ideals, grading, localization and dimension are defined inline or by the four definition nodes I opened. No proof is hidden in its statement.

Step 1 uses the NEW vertex lemma's actual maximality and equality of dimensions, and the definition of localization at a prime for the local ring, its maximal ideal and its residue field. The constant-component quotient is k; localizing k at nonzero constants changes nothing, so R is nonzero. The new statement does not rely on this item or its Hilbert conclusion. Step 2 uses the statements of the existing finite-type-algebra Noetherian and localization Noetherian leaves, both opened. A field is Noetherian because its only ideals are 0 and 1. The polynomial presentation is supplied by the finite generators, so both leaves have all their hypotheses; no algebraic closure or infinitude of k is used.

Step 3 uses exactly the generation and direct-sum grading of def-pc-standard-graded-algebra, which I opened: projecting a polynomial expression onto degree d shows that S_d is spanned by degree-d monomials. Factoring monomials proves the equality of the m-adic filtration with the degree tails, including j=0. This is an explicit elementary step, not a new lemma. Step 4 writes the degreewise comparison in the proof of 00P6: denominators have nonzero constant term, so reducing b/u modulo the next power leaves b_j/u_0. For injectivity the degree-j part of va is v_0a, and v_0 is a nonzero field scalar. These two formulas verify surjectivity and injectivity even with nilpotents, and include degree zero. No flatness or unquoted general localization theorem is used.

Step 5 uses the opened statement of lem-trf-maximal-adic-graded-length-bridge for the identity of colength with the sum of residue-field dimensions, and the opened statement of lem-trf-hilbert-samuel-growth-dimension for existence, positivity and degree of Q_R. The ring R has already been proved local, nonzero and Noetherian; its residue field is the given k. The former node is only used for its length formula, not for an argument inside its proof. The latter states exactly the needed degree equality. These are generic local-algebra tools filed in the trace chapter; their use is declared in split_report.tool_uses for maintainer judgment, with no top-level tool_uses edit. Step 6 uses the opened Mathlib leaf lem-trf-polynomial-infinite-evaluation-identity over the integral domain Q. All sufficiently large natural integers give distinct rational evaluation points. The same leaf compares Q with the eventual positive constant when the graded pieces terminate. We never take the natural degree of the zero polynomial or infer a positive dimension merely from S_0 nonzero.

Edge tests: S=k has m=0, R=k and cumulative polynomial 1, giving dimension 0. For k[t]/(t^r), r>=1, the same comparison works with nilpotents, the cumulative polynomial is eventually r, and localization at (t) changes nothing. For k[t], Q(n)=n and dim=1. For k[x,y], Q(n)=n(n+1)/2 and dim=2. A nonreduced or reducible homogeneous quotient requires no domain hypothesis: the source's homogeneous-minimal-prime argument puts every component through the vertex. Zero S is excluded by S_0=k, and finite fields cause no evaluation problem because the polynomial comparison is over Q. These cases also test the NEW vertex statement independently. I checked B–E: self-contained statement-only new node, definitions cited, ordinary TeX escaping, exact tags/labels, no duplicate or clause transfer, no cycle through the tangent-cone parent, actual statements supporting each citation, finite generation and nonzero/local hypotheses before each application. Every step is shorter than 2000 characters. No repair to the mathematical statement was necessary.

## Not duplicates

- lem-sfb-standard-graded-vertex-dimension vs lem-sbc-nowhere-dense-closed-fibre-dimension: strict dimension drop for a nowhere dense closed fibre does not identify global dimension with vertex-local dimension.

- lem-sfb-standard-graded-vertex-dimension vs lem-trf-flat-local-component-dimension-difference: flat local maps between essentially finite type algebras and transcendence degree differences do not assert the vertex attains global dimension.

- lem-sfb-standard-graded-vertex-dimension vs lem-sfb-standard-graded-cumulative-dimension: the item identifies dimension with cumulative polynomial degree; the new lemma has no polynomial and only identifies global and vertex-local dimension.

- lem-sfb-standard-graded-vertex-dimension vs lem-sfb-polynomial-zero-section-dimension: a polynomial extension zero-section point has local dimension shifted by the number of variables; no arbitrary standard graded quotient or vertex/global comparison is stated.

- lem-sfb-standard-graded-vertex-dimension vs lem-sfb-space-component-generic-chart-dimension: etale charts over generic points of algebraic-space components are different from localizing a graded algebra at its closed vertex.

- lem-sfb-standard-graded-vertex-dimension vs lem-sfb-point-tangent-cone-dimension: the parent compares a local ring to its associated graded tangent cone with geometric embeddings; it assumes smooth pointed ambient geometry and already uses this item. The new lemma is for arbitrary standard graded rings and compares their own global and vertex-local dimensions.

- lem-sfb-standard-graded-vertex-dimension vs lem-per-constructible-subset-closure-dimension: constructible subsets and their closures have equal topological dimension; it has no graded-algebra vertex statement.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-standard-smooth-over-field-dimension-at-points: requires a standard smooth presentation and computes n-c; the new lemma allows singular and nonreduced graded quotients.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-global-complete-intersection-equidimensional-lower-bound: bounds local dimensions of complete intersections; it neither applies to arbitrary standard graded quotients nor states that the vertex attains global dimension.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-global-complete-intersection-equidimensional: complete intersection equidimensionality assumes the expected dimension and says nothing about arbitrary graded quotients.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-lci-conormal-free-rank-codimension: conormal freeness after a local complete intersection presentation is different from global versus vertex-local ring dimension.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-dimension-at-point-components: expresses point dimension as a maximum over components THROUGH that point; it does not show that every component of a graded algebra passes through the irrelevant maximal ideal, which is the extra content of the new lemma.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-minimal-component-dimension-maximum: bounds dimensions of components below a chosen prime using the local dimension and residue transcendence degree; it does not establish that ALL components of a graded algebra lie under its vertex.

- lem-sfb-standard-graded-vertex-dimension vs lem-weil-pbc-closed-point-dimension-local-ring: identifies topological dimension at a closed point with the local-ring dimension, but does not identify it with the GLOBAL dimension as the new lemma does.

The existing homogeneous-primary-decomposition node concerns primary decompositions of polynomial-ring ideals; the projective affine-cone dimension node concerns cones of subsets in projective space. Neither gives the vertex localization theorem. Their statements and the associated-graded local-dimension node were also read.
