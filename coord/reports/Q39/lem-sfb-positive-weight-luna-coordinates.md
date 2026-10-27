# Stage-1 delivery: lem-sfb-positive-weight-luna-coordinates

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-positive-weight-luna-coordinates.json: statement split into eight proof steps; item is not a Mathlib leaf.
- citations.json: one verbatim statement quotation for each of the eleven step citations.
- report.md and searches.jsonl: review and actual search records. write_split.py is a sandbox-only JSON generation aid.

No new DAG nodes; no new Mathlib leaves. No Lean file was written and no compiler or build tool was run.

## Attachments

None. Searching lean/WeilConjectures by the exact blueprint tag and Luna/positive-tangent terminology found no declaration stating the item. The regularity and integrality declarations in WeilConjectures/AlgebraicGeometry/Regular.lean are supporting inputs, not proofs of this item.

## WANTED

None. Milne's iAG2017 and the Stacks source files needed here are available locally.

## Corrections and route

The imported statement is unchanged. Its proof was empty. The potential pitfall is the weight convention: the differentiated point action has the same exponent as a_i(tu)=t^{n_i}a_i(u), as the explicit calculation on the dual basis in step 3 shows. We do not identify this with the inverse-pullback action on a dual representation.

I read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The inherited branch supports the alteration/moduli argument through Milne's algebraic-group prerequisites. The present supporting tool does not change the unit's compactification route or its statement. The whole-blueprint searches for Luna, positive graded, and grading did not find a duplicate of this item. The inherited null nearest-blueprint-ancestor field was confirmed by tools/blueprint_refs.py ancestor; its explicit from.place and via chain are retained.

No statement dispute. The source first proves the irreducible case and subsequently treats merely connected varieties. Our item assumes smoothness everywhere, so regular-connected implies integral, allowing exactly the irreducible-case proof. There is no need to reproduce or rely on the later argument about different components.

## Not duplicates

No new nodes are proposed. In particular the existing lem-sfb-positive-graded-regular-polynomial supplies the homogeneous polynomial-algebra conclusion, and lem-weil-pbc-krull-intersection-localization supplies the required separation input. I initially searched the domain Krull-intersection theorem in Mathlib (the exact Ideal.iInf_pow_eq_bot_of_isDomain hit was returned), then found the existing DAG localization statement. Domain cancellation specializes that existing statement in two lines, so creating another Krull-intersection leaf would be redundant. The existing fixed-point-homogeneous-cotangent-lifts is not needed: this item already supplies its basis and lifts. Positive-weight-equivariant-inverse depends on this item and is not cited back.

## Mathlib searches

The searches.jsonl records every search actually executed. The item was searched with LeanFinder in two phrasings, LeanSearch, Loogle, and source grep using msearch.py. AffineSpace.isoOfIsAffine identifies affine space with a polynomial spectrum; it does not prove that our Z is affine space. I read its definition in Mathlib/AlgebraicGeometry/AffineSpace.lean:171 and nearby coordinate formulas. The second LeanFinder phrasing returned Algebra.Generators.exists_presentation_of_basis_cotangent and related bases; I read RingTheory/Extension/Cotangent/Basis.lean and its explanation: this is the conormal module of a presentation, rather than a global polynomial-algebra theorem from our tangent-weight hypotheses. The grep hits concern real calculus tangent cones, and Loogle returned no hits. Thus no exact theorem or one-line specialization proves this item. All inherited item search records were retained; fresh entries use exactly the logged queries.

## Unfinished work

None for this one-level stage-1 split. The existing cited nodes retain their independent proof obligations. This delivery does not claim a Lean proof of the item or of those nodes.

## Review by Q39

I read Milne, Algebraic Groups, iAG2017, Theorem 13.41 and its proof on printed pp.269--270, Lemmas 13.35--13.36 and Example 13.37 on pp.267--268, the coefficient comparison in Theorem 12.12 on pp.234--235, graded Nakayama 13.39 on pp.268--269, and Theorem 13.44 on pp.271--272. No new node requires a separate source review. For the reused algebra and scheme inputs I opened every cited node's statement and read the relevant Stacks text: 01T2 (morphisms.tex, lemma-locally-finite-type-characterize), 056S (varieties.tex, lemma-smooth-regular), 0569 and 033N (properties.tex, lemma-regular-normal and lemma-normal-locally-Noetherian), 01HV (schemes.tex, lemma-spec-sheaves), 01I4 and 01JQ (schemes.tex, affine fibre products), and 00IQ(1) (algebra.tex, lemma-intersection-powers-ideal-module). The Noetherian assertion of lem-wf-affine-noetherian-components is used exactly as stated, only after finite generation over a field is supplied by the affine-pairs node.

Step 1 uses lft-affine-pairs with U=Z and V=Spec F; both are affine. It uses affine-noetherian-components only for its first assertion, smooth-scheme-over-field-regular with the actual structure morphism, and regular-connected-integral after explicitly checking nonemptiness using z. The integral-scheme definition then gives that A is a domain. The spec-domain-stalks-function-field node is used only for clause (1), which states the localization identification even without assuming a domain; it supplies A_m=O_{Z,z}, so the regular local ring required later is present.

Step 2 uses fibre-product-affine-spectra for R=F, A and F[t,t^-1], and def-sc-gm-ga for the precise comultiplication t to st and counit t to 1. The coefficient calculation is written out: coassociativity makes each coefficient homogeneous, the counit recovers the element, and independence of Laurent monomials proves directness. This works for the infinite-dimensional coordinate algebra, unlike the existing finite-dimensional weight-basis statement. Fixedness of z proves homogeneity of the augmentation ideal. Thus no unquoted finite-dimensional representation lemma is being extended silently.

Step 3 is a dual-basis evaluation; it shows every n_i is positive with the intended point-action convention. Step 4 writes out the product surjection onto m^j/m^{j+1}; it is an elementary consequence of the supplied basis, not an unstated symmetric-power theorem. Replacing coefficients by residues uses m*m^j contained in m^{j+1}. Taking homogeneous components is legitimate because the grading and homogeneous powers have already been constructed. The empty basis case is included in that calculation.

Step 5 uses exactly the statement of krull-intersection-localization: it gives f outside m annihilating each element of the intersection by a possibly element-dependent power. I do not attribute an unqualified zero-intersection statement to that node. Noetherianness, finite generation of M=A as its own module, and primality of the maximal ideal are checked. Since f is nonzero in the domain A, cancellation supplies the desired zero intersection.

Step 6 explicitly inducts on the power of m, with base x in m; no nonpositive weight survives in a graded quotient by step 4. Separation from step 5 kills x. Subtracting the scalar x(z) treats weight zero, yielding A_0=F, not merely absence of negative degrees. Step 7 now checks every hypothesis of positive-graded-regular-polynomial: finite type, degree-zero algebra equal to the field, positive ideal exactly m, regular localization, and the actual supplied homogeneous basis. Its statement says the evaluation homomorphism for any such basis is an isomorphism, which is exactly the part quoted. The use is strictly smaller than the item, since the work deriving the positive grading from positive tangent weights and the original action is carried by steps 2--6.

Step 8 uses only the explicitly contravariant and functorial spectrum construction in def-weil-affine-spectrum to turn the inverse algebra map into an inverse to the stipulated lambda. It neither replaces the coordinate tuple nor merely constructs some isomorphism. I tested d=0, affine space with arbitrary positive weights, and polynomial shears such as weights (1,2) with coordinates x and y+x^2. The proof gives the specified inverse in each case. Zero or negative weights are deliberately excluded by the hypothesis: the induction in step 6 would then fail as it should. Nonreduced counterexamples are excluded by smoothness, and disconnected components are excluded by connectedness. Every argument is characteristic independent.

I checked delivery-errors B--E against the actual node and these sources. There are no statement-only new nodes to audit, no disguised replacement of the item by one new lemma, and no reverse citation of its parent. Each non-elementary fact is supplied by a cited statement; elementary coefficient, product, induction and inverse-map calculations are written explicitly. All step texts are below 2000 characters. The citation file copies actual statement text and includes every uses entry. Generic off-unit inputs (smooth regularity, connected regular integrality, affine stalks, affine products, and Krull localization) are declared in split_report.tool_uses with their role; no maintainer-owned tool_uses field is written. No forbidden SGA source is cited.
