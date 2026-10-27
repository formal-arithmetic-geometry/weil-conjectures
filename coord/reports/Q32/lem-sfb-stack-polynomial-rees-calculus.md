# Q32 stage-1 delivery: lem-sfb-stack-polynomial-rees-calculus

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-stack-polynomial-rees-calculus.json — statement; split into eight explicit construction/comparison steps; not a Mathlib leaf.
- dag/nodes/sec-six-functors-basics/lem-sfb-stack-qcoh-direct-sums.json — new statement-only node; arbitrary quasi-coherent coproducts, their scheme-test restriction, and the global-section comparison on a quasi-compact algebraic stack; no Mathlib match.
- citations.json contains a verbatim relevant statement excerpt for each of the 24 step-node citations. searches.jsonl and the ten raw search output files retain the searches actually run. report.md is this signed review.

No Lean, unit record, repository, or launcher file was changed. The one new node has no proof or proof dependencies and inherits the item's chapter and unit.

## Attachments

None. Searched the project's WeilConjectures source by the exact blueprint tag, item id and polynomial/sheaf/stack concepts. The existing scheme deformation/Rees files do not state the algebraic-stack result. Mathlib's ordinary ring Rees algebra is already represented by def-nagata-rees-algebra and is cited rather than duplicated.

## Wanted literature

WANTED: Jarod Alper, Adequate moduli spaces and geometrically reductive group schemes, local literature/alper-adequate-moduli-spaces-arXiv-1005.2398.pdf, Lemma 5.2.1 (printed p.507) and Lemma 4.1.8 (printed p.503), for lem-sfb-stack-polynomial-rees-calculus. The local file is absent. I read the published primary PDF online at https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf, especially printed pp.503 and 507, without downloading it into the repository. The expanded construction is marked proof_origin.by = agent.

## Audit of the imported material

The imported item was unsplit, with an empty proof and no lean_audit declaration. Its existing Mathlib searches, citations, source, blueprint provenance and statement are retained. I added only searches actually made with the prescribed msearch command; the raw results are saved in the sandbox. The ordinary Rees algebra hits are not stack polynomial-section comparisons. The second item phrasing found Ideal.span_pow_eq_map_homogeneousSubmodule, which is a ring-level coefficient statement; the short induction proving the corresponding finite-product description is explicitly included in step 5 instead of making another node.

The statement is unchanged. In particular it already specifies smooth-chart and global-section inclusions and disclaims inclusions on arbitrary nonflat tests. This is essential: images and powers are taken in QCoh, not as image subfunctors in all sheaves on the big site. For example on Spec k[t], the QCoh inclusion (t) into k[t] becomes the zero map k to k on the test Spec k obtained by t=0, so it is not an objectwise injective map on all tests. Steps 4 and 8 make the correct image and global-section meanings explicit. This is not a new disputed statement or a weakened conclusion.

## Source error

The displayed construction in the published proof of Alper Lemma 5.2.1 uses a direct sum indexed by n>0. A positive-degree ideal alone has no unit in general (take I=0 in a nonzero ring). The assigned item already repairs this by using n>=0. The delivery retains that repair, includes B in degree zero, and makes the degree-zero map the identity. No adequate-affineness hypothesis is used in this auxiliary polynomial/Rees construction: Alper uses that extra hypothesis only after constructing the surjection, to obtain adequacy of its section map. I make no assertion that the section map is surjective.

## Blueprint and route

Read the chapter and the unit record and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, especially (3). The current blueprint describes the compactification/direct-image route; the long auxiliary alteration/moduli ancestry in this assigned item is retained as imported provenance. No unit step is replaced. blueprint_refs.py ancestor returned null for the nearest imported ancestor of this existing auxiliary chain; the new node consequently retains from.node = null and prepends this item to the existing via list. Searches across all imported blueprint nodes for Rees, direct sums, coproduct, filtered colimits, quasi-coherent, 06WN and 0GQV found no matching stack module-coproduct statement. The ordinary ring Rees definition is reused.

## Not duplicates

lem-sfb-stack-qcoh-direct-sums vs lem-sfb-groupoid-module-descent-tensor-cokernel: the existing node gives a quotient-groupoid equivalence, tensor products and cokernels; it does not assert arbitrary coproducts or their global sections on a quasi-compact algebraic stack.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-finite-type-stack-affine-smooth-atlas: the existing node constructs a finite-type affine atlas, with an extra finite-type assumption; the new node states a module coproduct and section comparison, with no finite-type assumption.
lem-sfb-stack-qcoh-direct-sums vs def-sfb-finite-stack-scheme-tests: the existing node defines finite maps, finite diagonals and finite-type etale atlases, not module coproducts or sections.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-algebraic-stack-quasicompact-surjection: the existing node characterizes quasi-compactness by atlases and surjections; the new node concerns quasi-coherent modules and the behavior of global sections.
lem-sfb-stack-qcoh-direct-sums vs def-sfb-stack-qcqs-morphism: the existing node defines quasi-compactness and quasi-separatedness, not existence or sections of module coproducts.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-stack-quasicompact-absolute-criterion: the existing node compares absolute quasi-compactness with a structural morphism; the new node is the module coproduct/sections theorem.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-dm-quasicompact-atlas-criterion: the existing node characterizes quasi-compactness for DM stacks; the new node applies to arbitrary algebraic stacks and asserts a module-theoretic conclusion.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-affine-groupoid-quasicoherent-algebra-descent: the existing node describes algebras and invariants for an affine finite-locally-free groupoid, not arbitrary families of modules on general stacks.
lem-sfb-stack-qcoh-direct-sums vs lem-sfb-stack-polynomial-rees-calculus: the new node is a general additive module result for arbitrary families, with no polynomial variables, ideal, grading, Rees algebra or presentation map. The item's proof still constructs all of these, their multiplication and the coefficient formula; it is not reduced to applying a restatement of an item clause.

## Review by Q32

I read Alper's published proof of Lemma 5.2.1 and the polynomial comparison in Lemma 4.1.8. For the new module node I read Stacks stacks-sheaves.tex Tag 06WN, lemma-qc-colimits (1) and its scheme-restriction proof, and stacks-properties.tex Tag 04YC, lemma-quasi-compact-stack (2),(3). The coproduct existence and restriction statements are exactly the relevant colimit assertions. The section consequence uses a genuine finite-support descent argument: choose a quasi-compact smooth atlas, replace it by a finite union of affine opens, and restrict a section of the sheaf coproduct there. Each affine restriction has only finitely many nonzero coefficients; their finite union is a uniform finite set. Global projection maps extract coefficients in Gamma(X,F_a). Subtracting the corresponding finite sum gives zero on the atlas and hence zero globally, by descent. Injectivity follows by applying the projections. This works without quasi-separatedness of the overlaps and for varying modules F_a, not merely copies of an algebra. This is the argument to be proved when the new statement-only node is itself split.

For step 1 I opened the statements of the new direct-sum node, stack-qcoh-flat-atlas-exactness, stack-quasi-coherent-scheme-restriction, and the existing polynomial-ring definition. They give respectively the coproduct/restriction, tensor closure and faithful tests, the scheme interpretation with tensor compatibility, and the precise finite-monomial polynomial multiplication. The step constructs the multiplication on pairs of summands and checks every algebra identity on smooth charts; it does not invoke a nonexistent polynomial descent theorem.

For step 2 the direct-sum comparison is applied only after proving quasi-compactness from the definition of the given morphism, using the identity test Spec P. The polynomial definition identifies finite monomial expansions and the multiplication, so this is a ring comparison and is natural on coefficients. No quasi-separatedness of an absolute diagonal or Noetherian assumption is inserted.

Step 3 uses only the new node's assertion that the sum is a sheaf coproduct, and the exact local-lifting meaning of surjection in stack-quasi-coherent-algebra. There are finitely many coefficients locally, so finitely many successive covering refinements suffice. It is elementary local lifting and not an exactness assertion about Gamma.

For step 4 I opened stack-qcoh-abelian, stack-smooth-qcoh-exact, and stack-qcoh-flat-atlas-exactness. The first gives the category in which the image is taken; the second explicitly preserves images via kernels/cokernels on smooth charts; the third gives tensor closure, module-sheaf cokernels, and faithful atlas restriction. Those statements support the image, ideal action and quotient used. I also read their Stacks sources, 06WV and the smooth-specialization content of 076X and 0GQF. The nonexactness warning preceding 06WV is why the big-site image was not substituted for the QCoh image.

For step 5 the same statements supply sums, images, tensors and exact smooth restriction. The new content is written explicitly: e_m is the sum of all degree-m generator products, m=0 is the identity, and splitting off one factor proves both inclusions of the recurrence. Multiplication of two generator products is given by addition of their finitely supported exponents. This is the finite elementary ideal calculation, even with an infinite generator index. Faithful exact restriction detects equality of the image subobjects; an arbitrary nonflat test does not.

Step 6 reuses those direct-sum and faithful-test statements, and def-nagata-rees-algebra gives exactly the ordinary coefficientwise Rees algebra identified on charts. I read its Mathlib match reesAlgebra and mem_reesAlgebra_iff in Mathlib/RingTheory/ReesAlgebra.lean, lines 39 and 64. The degree-zero and generator maps of q are constructed, and the multiplication identity is written. This is a definition/Mathlib tool and does not change the unit's route.

Step 7 uses the precise epimorphism/local-surjectivity clause of stack-qcoh-flat-atlas-exactness, applied to each e_m onto its image. The rest is the elementary finite-cover refinement argument already justified for sheaf sums. It proves surjectivity of q as sheaves and deliberately proves no surjectivity of Gamma(q).

Step 8 uses the general direct-sum theorem, then identifies global sections with Hom from O by sending 1 to a section, using the compatible-family convention in the algebra definition. Cancelling the QCoh image monomorphism proves the needed injection on global sections even though the big-site inclusion is not left exact. The resulting coefficientwise algebra multiplication and the explicit summand map defining q give the claimed formula, including degree zero.

Small cases checked: empty variable sets give B; the empty generator family forces I=0, K_0=B and K_m=0 for m>0; the zero ideal therefore gives R=B and a constant presentation. For the unit ideal generated by 1 one gets R=B[T] and x maps to T. For a nilpotent ideal in k[epsilon]/(epsilon^2), the second and higher powers vanish and the formula is compatible with that relation. Infinite generator and variable families still give finite supports per section because X is quasi-compact. Dropping quasi-compactness would fail on the disjoint union of countably many points, where one can place a different monomial on each component; the new module statement retains this necessary hypothesis for its section clause. The empty stack gives zero section modules and the zero ring throughout. Non-affine and non-separated overlaps cause no problem: the proof never declares overlaps affine. In positive-characteristic quotient stacks nothing requires exact invariants or exact global sections. The explicit k[t] nonflat test above checks the inclusion caveat.

All eight proof steps are shorter than 2000 characters (1213, 742, 711, 1157, 1302, 931, 605, 1136); none hides a long comparison argument. Every statement used in a step was opened and is quoted verbatim in citations.json. The new node is a real general module input, not a polynomial or Rees clause moved out of the item. B1-B10, C1-C8, D1-D5 and E1-E7 were checked against the files and sources; the mathematical issues addressed are finite support, correct image category, exact smooth restriction, and the unital degree-zero convention.

## Unfinished work

No part of this stage-1 split is left unfinished. The new module theorem is intentionally statement-only and joins the stage-1 queue. Lean remains untouched. Server validation and direct delivery follow this review.
