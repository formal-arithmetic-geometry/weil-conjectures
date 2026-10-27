# Stage-1 report: lem-sfb-projective-space-pseudocoherence-twist-test

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-space-pseudocoherence-twist-test.json`: item split into five proof steps; statement unchanged; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-projective-space-tilting-equivalence.json`: new statement-only prerequisite, Stacks 0BQU with the explicit algebra, total derived tensor and global-derived-Hom inverse; no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-free-algebra-pseudocoherent-resolution.json`: new statement-only prerequisite, Stacks 0CSF; no Mathlib match.
- `citations.json`: a verbatim statement quotation for each citation in each item proof step.

## Attachments

None. I searched the project source by the exact blueprint id and by pseudo-coherence, tilting, Beilinson, endomorphism-algebra and finite-free algebra/resolution terms. The existing project declarations concern other pseudo-coherence criteria, projective space geometry, or generic homological algebra; none states this finite-twist criterion. No Lean source was changed or compiled.

## WANTED

None. All sources needed are in the read clone.

## Audit findings and changes

The item is exactly implication (5) => (1) of Stacks 0CSG, `perfect-lemma-pseudo-coherent-on-projective-space`. I kept its statement and statement dependencies. The proof follows the source's endomorphism-algebra route, rather than appealing to a new node restating the twist criterion. The two new nodes are independent prerequisites: a derived equivalence for every complex, and a resolution theorem for every finite-free algebra over its base. Neither has the item's twist hypothesis or its pseudo-coherence conclusion on projective space.

The initially investigated additional node `lem-sfb-projective-complex-bimodule-derived-tensor` was not created. The existing `lem-trf-bounded-above-acyclic-derived-computation` already says that a bounded-above complex of projectives computes any existing total left derived functor of an additive right-exact functor. Step 5 applies that statement to sheafified balanced tensor. Its searches remain in the unmodified search log as research, but there is no extra DAG node.

The source proof of 0CSF says “smallest index” for its nonzero cohomology, although the argument starts at the largest possible degree and descends. It also has an incidental K/M variable slip. These do not change its true theorem statement; I created only that statement, and its future proof must start from an upper cohomological bound. In the final paragraph of 0CSG the printed filtration has truncation indices pointing the wrong way for a bounded-above complex; the intended exhaustion is by truncations starting at successively smaller degrees. The item avoids depending on this notation by citing the existing total-derived-computation lemma explicitly.

`tools/blueprint_refs.py ancestor` reports `None` for the item's inherited `created.item` chain. I preserved its existing null ancestor, descriptive place, and complete via chain; the new nodes prepend this item to that same chain. This records the actual tool output rather than inventing a blueprint ancestor. I read the latest blueprint's chapter and unit/direct-image proof, including `det-thm-sf-ctf-stability-direct-images` clause (3); this criterion is a prerequisite of the inherited alteration/pointed-curve/relative-image route. The item is not the key statement of its unit, so no unit realization fields are changed.

## Mathlib and duplicate searches

For the item and each new node I ran LeanFinder, LeanSearch, Loogle and grep with the prescribed msearch command, plus a second LeanFinder phrasing. Queries and returned declarations are preserved in `searches.jsonl`, `search-*.txt`, and the node fields. All services answered on this run. The hits are general K-projectivity, projective dimension, left derived functors of objects, ordinary tensor-Hom equivalences, Picard groups and finite algebras; none is an exact or one-line match for the two new prerequisites. I read `CochainComplex.isKProjective_of_projective` at Mathlib/Algebra/Homology/HomotopyCategory/KProjective.lean:113 and `CategoryTheory.ProjectiveResolution.isoLeftDerivedObj` at Mathlib/CategoryTheory/Abelian/LeftDerived.lean:111: the first proves K-projectivity, and the second computes cohomological left derived functors of an object, so neither is a substitute for the new statements. That review led to reusing the existing broader DAG computation lemma.

I searched all `dag/nodes` by 0BQU, 0CSF, 0CSG, the Stacks labels, tilting, Beilinson, endomorphism algebra and finite-free noncommutative resolutions, and used `tools/blueprint_refs.py search` for projective space, tilting, pseudo-coherent, endomorphism algebra, finite free algebra, the tags, and projective resolutions. No duplicate of either new node was found. The noetherian proper/coherent projective-space finiteness statements do not imply this criterion over arbitrary rings.

## Not duplicates

No existing node has tag 0BQU or 0CSF. The existing 0CSG-tagged nodes are the item and its parent `lem-sfb-relative-section-image-flat-fp`; neither is a duplicate of a new node. The new equivalence makes no pseudo-coherence assertion, and the new algebra resolution statement does not involve a scheme or twist.

## Review by Q40

I read Stacks `perfect.tex`, `lemma-pseudo-coherent-on-projective-space` (0CSG), the preceding algebra resolution lemma (0CSF), and `lemma-Pn-module-category` (0BQU), including the displayed generator and triangular endomorphism algebra. For the derived-Hom inverse and existence of total tensor I also read `dga.tex`, `lemma-tensor-with-complex-derived` (09LX) and `lemma-tensor-with-complex-hom-adjoint` (09LY). Thus both new statements specify their own objects, coefficient ring, right-module convention, derived categories and all hypotheses. The inverse is a statement about derived objects, not a list of unrelated cohomological identifications. They are left unsplit with no proof sketch in their statements.

Step 1 uses exactly the new equivalence statement, including its RHom inverse after restriction of scalars. Essential surjectivity applies because K has quasi-coherent cohomology; no boundedness is assumed or smuggled in. The algebra acts on T on the left, so RHom(T,K) has the required right action by precomposition.

Step 2 uses `def-pc-projective-space-twist` for the standard-open bases and inverse transition functions, and `def-pc-perfect-complex` to recognize T as strictly perfect on these opens. I opened `lem-pc-perfect-rhom-tensor-comparison` and checked that it provides the full derived tensor/Hom isomorphism for a perfect first argument and a quasi-coherent second argument, not merely the existence of a dual. `def-pc-global-derived-rhom` defines precisely the global Hom used in Step 1; `def-pc-scheme-derived-tensor-structure` fixes the additive derived tensor. The finite biproduct argument is written using inclusions and projections; it involves only finitely many terms and uses no assertion that derived global sections preserve arbitrary coproducts.

Step 3 uses exactly the finite-free bounded-above definition in `def-pc-ring-pseudo-coherent-complex`. It proves closure under this finite sum directly, by the maximum of finitely many upper bounds and finite termwise ranks. I marked this step elementary and introduced no closure node.

Step 4 uses the explicit algebra description in the new tilting node and the conclusion of the new 0CSF resolution node. The finite-free base hypothesis is verified block by block on monomials; commutativity is required only for the base R, not for the triangular algebra B. No noetherian hypothesis appears. This step applies the lemma to a right B-module complex, matching its convention.

Step 5 uses the existing `lem-trf-bounded-above-acyclic-derived-computation` statement, which I opened in full: its hypotheses are enough projectives, additive right-exact V, existence of its total left derived functor on all objects, and a bounded-above projective complex. I verified these respectively by free modules and basis lifting, the balanced-tensor cokernel presentation and exact sheafification, the new tilting node, and the finite-free terms of F. The explicit tensor identification sends a vector tensor t to the vector of its coefficients acting on t. Standard chart bases then trivialize every term on the same open, even though F is unbounded below. Finally `def-pur-pseudo-coherent-complex` says precisely that such local bounded-above finite-free representatives suffice. The two off-unit generic tools are declared in `split_report.tool_uses` with their roles.

For the edge cases I checked N=0: T is the structure bundle, B=R and the argument is the affine criterion; R=0 gives empty projective space and zero module categories; K=0 admits the zero resolution. The new algebra lemma allows a rank-zero algebra only when its unital module category is zero, where the claim is still valid. Negative cohomological degrees are unrestricted; a bounded-above complex may be unbounded below. I also checked the opposite-action convention and the fixed-degree monomial finiteness over a nonnoetherian base. All five steps are below 2000 characters, and no new node repeats a clause of the item. This is my author review under the direct-delivery brief.

## Unfinished work

None in the requested one-level split. The two new prerequisite nodes remain statement-only for their own future stage-1 work.
