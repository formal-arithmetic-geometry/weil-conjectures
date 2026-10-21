# Stage-1 worker report

Item: lem-weil-pbc-direct-image-roos-normalization. Group NX. Date 2026-10-21.

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-direct-image-roos-normalization.json — statement, split into eight proof steps; not a Mathlib leaf.
- citations.json — 26 records copying the statement used by each step verbatim.
- report.md — this report. searches.jsonl contains six searches executed through msearch.py; prepare.py is a sandbox-only preparation script.

There are **0 new nodes and 0 new Mathlib leaves**. No unit, chapter, repository, launcher, or Lean file was written. No compiler, Lake, build, or git command was run.

## Attachments

None. Searches in lean/WeilConjectures/ for the blueprint tag, direct-image/Roos combinations, strict-Roos comparisons, and underived-composite normalization found no declaration proving all clauses of this item. The affine-section direct-image normalization declarations have different objects and statements. Sorry declarations were not accepted as attachments.

## WANTED

None.

## What required correction

The item was unsplit, with an empty proof. Its statement, original searches, provenance, and blueprint fields are retained. The split proves the specified first component, not just existence of a cone isomorphism. It also proves the connecting square in coordinates, rather than inferring it from the product square.

No STATEMENT-DISPUTED change is needed. The ringed-topos statement does not impose commutativity on the rings. In reviewing candidate dependencies I avoided using lem-weil-strict-roos-comparison, which assumes commutative rings, and lem-pc-derived-functor-termwise-split-ses-triangle, which assumes ringed spaces. The proof instead uses the existing general abelian-category lem-weil-pbc-exact-products-roos-comparison and lem-pur-roos-additive-comparison. The former uses the negative of our transition map; the explicit sign isomorphism in Step 5 preserves the normalizing inclusion and resolves this convention difference.

## What could not be finished

Nothing remains in this stage-1 split. The cited open nodes remain their owners' items.

## Sources and searches

I read sites-cohomology.tex, Tags 0940/0941 (tower site, K-injective evaluation, product sequence), and Tag 0A07 (both proofs). The first proof gives the common underived composite normalization. The alternate proof assumes enough points; no such hypothesis is used here. Exact module pullback in the item permits the direct K-injective adjoint argument instead. I also read derived.tex Tag 0BK6 (termwise products represent derived products), Tag 08BJ (exact-left-adjoint preservation of K-injectives), and Tag 0152 with the cone formula and its naturality calculation; injectives.tex Tag 079P gives functorial K-injective resolutions with injective terms. I inspected the source rightDerivedFunctor triangulated construction in WeilConjectures/CategoryTheory/DerivedCategory/RightDerivedFunctor/Triangulated.lean, including its realization through K-injectives. The explicit normalized cone calculation is agent-written, and proof_origin is marked accordingly.

I read the current main-20261015 blueprint proof of prop-weil-pbc-direct-image-limits, the chapter and unit records, and the item's existing statements. This realizes the product/Roos/one-minus-transition sentence, staying below that blueprint node. Whole-DAG and blueprint searches for Roos, mapping cone, and direct-image limits located the reusable cone and comparison nodes; no duplicate was created.

The item's inherited NI searches are preserved. NX ran leanfinder twice (the normalized derived-limit comparison, then the K-injective cone-triangle comparison), loogle for CochainComplex.mappingCone.mapTriangleIso, grep twice in CategoryTheory and Algebra/Homology, and leansearch for the exact-adjoint derived-limit statement. All six completed successfully. I read the hits, including Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:441 (mapTriangleIso) and its boundary calculation at lines 419–430. That theorem is an ordinary complex cone comparison. It neither constructs the ringed strict-tower derived composites nor identifies their normalized comparison, so it does not attach the item or make it a Mathlib leaf. Exact-functor derived-category hits also do not apply directly: G need not be exact.

## Not duplicates

No new nodes; there are no new/existing node pairs to distinguish. In particular, the generic cone calculations are steps using existing nodes, not new nodes restating this item's clauses.

## Review by NX

I checked delivery-errors B–E against the statements and the sources, including the repeated historical section. Each citation below is to its statement, not to an extra assertion in its proof. citations.json contains every use, with an unmodified contiguous quote; no source reference substitutes for a node dependency.

Step 1 uses lem-weil-pbc-small-module-diagrams-grothendieck for the Grothendieck property of strict towers, lem-pur-kinjective-degreewise-existence for the actual resolution with injective degree terms, and lem-weil-tower-evaluation-kinjective for its evaluations. The index is countable and small in the module universe, and both sites are small, so the size hypotheses hold. The first lemma permits noncommutative ring sheaves; the resolution theorem is for a general Grothendieck abelian category. I verified the degree-term assertion in Tag 079P.

Step 2 uses lem-weil-tower-category-levelwise-abelian to check exactness of F on towers and of the constant-tower functor, lem-weil-pbc-right-adjoint-preserves-kinjective for J, GI_n and the two ordinary limits, and the defining extension property in def-sp-injective-resolutions to prove preservation of injective degree terms explicitly. These are exact LEFT adjoints; exactness of G is never asserted. The step then uses lem-weil-pbc-kinjective-total-derived, whose statement specifically says the comparison is invertible on K-injectives. The levelwise adjunction and the constant-tower/limit adjunction are checked by componentwise Hom bijections.

Step 3 uses exactly the universal property in def-weil-category-product. The Hom bijections write out the product preservation argument and the corresponding compatible-family argument for limits. Degreewise uniqueness proves compatibility with differentials and gives inverse comparisons. This is an elementary application of the assumed adjunction, with no separate preservation theorem hidden in the step.

Step 4 uses lem-pc-ringed-space-product-kinjective. Despite its name, I checked that its statement applies to arbitrary abelian categories, not just ringed spaces. It supplies both K-injectivity and the derived-product universal property. The adjoint K-injective and total-derived computations identify the product comparison's actual components. The one-minus-shift square is checked after every projection using def-weil-tower-transition-endomorphism and def-weil-category-product; it uses additivity of module direct image and the actual strict transitions.

Step 5 uses the coordinates defined by def-weil-strict-roos-model, the general Hom exactness statement of lem-weil-pbc-hom-into-triangle-exact in the homotopy category, and the cone/rotation convention in def-weil-abstract-derived-category. Shifts of a K-injective satisfy the same null-homotopy condition because shifts of acyclic complexes are acyclic. Rotating the cone triangle then proves the vanishing needed for the cones. The general lem-weil-pbc-exact-products-roos-comparison supplies the unit normalization; its hypotheses are checked separately on A and B, and the sign is changed explicitly. Its composite-with-kernel-inclusion clause, together with invertibility of the derived unit on I and J, proves the required inclusion maps invertible. I do not use a commuting-projections assertion to infer equality of maps to a homotopy limit.

Step 6 uses the statement of lem-pur-roos-additive-comparison, including its actual diagonal biproduct/product coordinates. Step 3 verifies that theorem's product-comparison hypothesis for every strict tower complex. The displayed differential calculation and the zero/limit-leg calculation prove both the chain comparison and its agreement with j_I and j_J. This is a general abelian-category tool and is not a new node containing the desired theorem.

Step 7 verifies the last square explicitly. For the rotated cone triangle the first arrow is the second-coordinate projection and the boundary is the first-coordinate inclusion. Applying the diagonal cone map gives the equations on both coordinates, including the zero coordinate. I checked the signs against the -p boundary and inverse rotation convention. The canonical shift structure from lem-pc-right-derived-functor-triangulated is computed termwise on the K-injectives, so this is the derived connecting square with its shift comparison. The triangulated node is unbounded; the similarly named bounded-below direct-image node was not used.

Step 8 uses the statement of lem-weil-ringed-tower-pushforward-limit-comparison verbatim: it normalizes its comparison by the equality of underived composite direct images. Since L_I and J are K-injective for the respective next operations, the comparison is the actual ordinary-limit comparison beta on this representative. The equation theta G(j_I)=j_J beta then identifies the first cone component with that beta, rather than choosing an unspecified cone completion. It transports all three checked squares to the prescribed first map. Localization and K-injective computation make this representative computation valid for every derived strict tower; naturality follows from the displayed product/limit and diagonal coordinate formulas.

I tested the argument on zero towers and the zero ring (every comparison is the unique identity of a zero object), on identity direct image (the comparisons and cone map are identities), on a constant tower with identity transitions (the zero-coordinate inclusion retains the actual augmentation), and on a tower with zero transitions (u=1, so the cone is contractible and the limit comparison still has its specified normalization). I also checked the negative-u sign conversion and did not use boundedness, enough points, or a functorial cone on an arbitrary triangulated category. Every proof step has fewer than 2000 characters. No clause was moved into a new node, no proof dependency refers back to this item, and every off-unit generic tool used is declared in split_report.tool_uses for the maintainer's route review.
