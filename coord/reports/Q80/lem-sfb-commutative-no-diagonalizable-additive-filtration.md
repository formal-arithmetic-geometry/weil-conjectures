# Stage-1 delivery: lem-sfb-commutative-no-diagonalizable-additive-filtration

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-commutative-no-diagonalizable-additive-filtration.json`: item, split into four steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-commutative-diagonalizable-unipotent-product.json`: statement, unsplit; Milne's general commutative product decomposition with unitriangular realization of its unipotent factor; no Mathlib match.
- `citations.json`: nine verbatim statement quotations, one for every cited node in every step.

One new node, zero Mathlib leaves. The new node has no proof or proof dependencies. Its statement introduces every object and defines diagonalizable and unitriangular explicitly. No Lean was written or compiled; no repository or launcher file was changed.

## Attachments

None. Searched the project Lean source for the exact item id and for additive filtration, diagonalizable, multiplicative type, and unipotent. The incidental unipotent biproduct matrix and the word diagonalizes do not state the item or the new decomposition result.

## WANTED

None. Milne's book is available locally and was read with pdftotext.

## Problems found

No mathematical error in the item, and no statement correction. Its source names 16.13(a); I also used 16.13(b), which applies over the algebraically closed base and gives a concrete product identification, avoiding a separate quotient-by-trivial-subgroup comparison lemma. This stays within the source's commutative structural reduction to the intersection proof of 14.21.

The inherited blueprint chain has `from.node: null`. `tools/blueprint_refs.py ancestor lem-sfb-commutative-no-diagonalizable-additive-filtration` likewise prints None. Its detailed `from.place` explicitly traces det-thm-sf-ctf-stability-direct-images proof (3) through the intervening alteration, moduli and group-theoretic inputs. I preserved that ancestry and extended its place for the new structural input, without inventing a different nearest ancestor. I read the current `literature/blueprint/latest/.../sk-thm-sf-ctf-stability-direct-images.proof.md`, especially (3), as well as the chapter and unit records. No chapter or unit route was changed.

## Not duplicates

lem-sfb-commutative-diagonalizable-unipotent-product vs lem-sfb-commutative-no-diagonalizable-additive-filtration: the new result applies to every commutative affine finite-type group, with no assumption on its diagonalizable subgroups, and gives a product decomposition and matrix embedding, not an additive filtration. The item's argument must eliminate the diagonalizable factor, intersect coordinate subgroups, factor each restricted homomorphism, and reverse the chain.

lem-sfb-commutative-diagonalizable-unipotent-product vs lem-sfb-geometric-unipotence-unitriangular-embedding: the existing result assumes smoothness and an already given faithful representation with unipotent geometric points; it does not split arbitrary nonreduced commutative groups or construct their diagonalizable factors. In particular it cannot be applied to the item as stated.

lem-sfb-commutative-diagonalizable-unipotent-product vs lem-sfb-commutative-multiplicative-type-extension: the existing result concerns an extension whose kernel and quotient are both of multiplicative type, not the existence of a diagonalizable/unipotent decomposition of an arbitrary commutative group.

lem-sfb-commutative-diagonalizable-unipotent-product vs lem-sfb-multiplicative-type-largest-subtorus: the existing result starts with a group of multiplicative type and extracts its torus; it does not assert any unipotent complement or decompose arbitrary commutative groups.

The whole-DAG searches for source 16.13 and for a largest multiplicative subgroup/product with a unipotent factor found no existing decomposition node; 16.13 occurs as an item source. Searched whole imported blueprint using blueprint_refs for unipotent, multiplicative plus unipotent, commutative plus group, and unitriangular. No blueprint statement gives the new decomposition or the item. Keyword hits for representation theory, smooth unipotent groups and Lie algebras were read and rejected for their different hypotheses and objects. The source is Milne, so there is no new Stacks-tag collision.

## Mathlib searches

All new searches used the required msearch.py wrapper and are recorded in searches.jsonl. The node records the exact queries and returned log summaries. Two decomposition phrasings in LeanFinder, a decomposition query in LeanSearch, the Loogle GroupScheme/unipotent query, and the AlgebraicGeometry grep found no group-scheme match. The strongest hits are Module.End.exists_isNilpotent_isSemisimple and LieModule triangularizability, which concern a single endomorphism or Lie-module action and cannot produce a decomposition of a possibly nonreduced group scheme. A second item phrasing and the unipotent central-series query returned abstract nilpotent group series and profinite quotients; these have no scheme structure, closed immersions or fppf quotient maps. The grep queries in AlgebraicGeometry and AlgebraicGeometry/Group were empty. All services answered successfully; none is recorded as unavailable.

## Review by Q80

I read Milne, Algebraic Groups (2017), Theorem 16.13 and its proof on printed p.328, Proposition 14.21 and its intersection proof on pp.284--285, and Theorem 14.5 on p.281. For the only new node I checked 16.13(b): algebraic groups here are not assumed smooth or connected, and the algebraically closed field is perfect. The multiplicative-type factor is diagonalizable over this base, as in Section 12.14 and Theorems 12.8--12.9 (pp.233--236). Theorem 14.5(b) gives an actual closed subgroup of a unitriangular group, rather than a condition only on geometric points. This distinction matters for alpha_p and mu_p.

For step 1 I opened the new decomposition statement. It supplies closed D and U, an isomorphism by multiplication, and a closed unitriangular embedding of U. The hypothesis of the item forces D=1 as a group scheme. The inverse and projection described in the step identify G with U; no smoothness hypothesis has been slipped in. This step uses a general structural theorem, not a new copy of the item's filtration conclusion.

For step 2 I opened lem-sfb-unitriangular-coordinate-filtration. It supplies exactly the finite indexed coordinate series, its closed subgroup property, endpoints, and coordinate homomorphisms, over an arbitrary field and without restricting G to smooth groups. I also read the statements of def-sc-group-scheme-subgroup, def-weil-closed-immersion, and def-weil-finite-type-morphism: these justify the pointwise subgroup test, affine quotient equations, and finite algebra generation used in constructing H_r. The equations A/(x_1,...,x_r) make the inverse images and nested closed embeddings explicit. The endpoint H_m=1 uses that the embedding i has trivial scheme-theoretic kernel, not the incorrect inference that a group with one geometric point must be trivial. This is a routine intersection construction from the cited coordinate series and definitions, so no new intersection lemma is needed.

For step 3 I opened lem-sfb-algebraic-group-homomorphism-factorization and checked all its hypotheses: H_{r-1} and Ga are finite type and separated, with separatedness supplied by the exact statement of lem-weil-pbc-affine-source-morphism-separated for their affine sources. The coordinate-filtration statement supplies that the restriction of p_r is a homomorphism; its kernel is the explicit next coordinate equation. The homomorphism theorem's statement supplies a CLOSED image embedding, a faithfully flat FINITELY PRESENTED quotient map, its scheme-theoretic kernel, and its represented fppf sheaf quotient. Thus I use its statement, not an argument inside its proof. The image is affine by the affine-quotient characterization of closed immersion in def-weil-closed-immersion, whose statement I read. There is no unsupported assumption that a restricted coordinate projection remains surjective onto all of Ga.

Step 4 is index reversal with r=m-j+1. I checked that its domain H_{r-1}=G_j and kernel H_r=G_{j-1} have the correct order; each quotient from step 3 has exactly the required data. This step needs no new lemma. No non-elementary proof step exceeds 2000 characters (lengths 400, 904, 770, 416). The proof-dependency union and all nine citation quotes were checked. Only the assembly and affine coordinate intersection steps are elementary.

Small cases: the trivial group admits the explicit length-zero chain, including n=1 and m=0. Ga admits the obvious additive factor. In characteristic p, alpha_p is allowed, with its nonreduced closed embedding into Ga; the construction never discards its nilpotents. The constant group Z/p is also an allowed disconnected closed subgroup of Ga (the equation t^p-t=0), so connectedness is not used. A nontrivial mu_p or Gm fails the item's hypothesis but is included in the new decomposition with U=1 and D the whole group. The product alpha_p times mu_p is likewise covered by the new theorem; it is not erroneously classified as unipotent by geometric points alone. Repeated coordinate terms yield trivial quotients, which are permitted by the non-strict chain in the item.

I checked delivery-errors B--E: the new node is self-contained and statement-only, all non-elementary facts are node citations that supply the claimed conclusions, no definitions are cited for stronger theorems, no new node repeats an existing statement or merely exports the item's conclusion, and no quotient is asserted from rational-point surjectivity. The statement dependencies of the item were retained. All proof citations stay in the same unit except definitions, so no additional off-unit tool use is requested.

## Unfinished work

None for this one-level split. The new decomposition theorem is deliberately unsplit and joins the stage-1 queue. Delivery awaits the required dry run and push.
