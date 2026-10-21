# Stage-1 delivery: lem-sfb-finite-valued-cech-cocycle-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-finite-valued-cech-cocycle-descent.json: statement node, now split in eight steps; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for all three proof-step citations.
- report.md and searches.jsonl: review and actual logged searches.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, finite-valued, finite Cech, and cocycle/profinite combinations found no declaration giving this statement. The etale finite Cech coefficient declarations concern schemes and coefficient comparisons, not finite quotients of a profinite surjection. No Lean was written or compiled.

## WANTED

None.

## What was wrong

The imported node was statement-only, not an accepted split. Its statement is correct and unchanged, including all empty-space and zero-group cases. Its blueprint.from.node is already null and its inherited via chain ends at an agent-created ordinary-direct-image input; blueprint_refs.py ancestor also reports None. I retained that provenance, its existing precise paragraph (3) reference and same_as [], and made the split_report explain the place served. The stored unit is the older sk-thm-sf-ctf-stability record whereas the source paragraph is the current basic-constructions direct-images proof. This delivery does not silently replace either route or edit the unit. The topological argument supplies exactly the finite-discrete reduction of the parent normed-scalar Cech exactness proof.

The main possible false inference is surjectivity on finite-quotient fibre tuples. The proof avoids that inference explicitly: a tuple at the quotient has representatives whose images are in one base partition block, which need not be one point of S. The compact defect-locus construction ensures the equation for precisely these representatives.

## New nodes

None (0 new nodes, 0 new Mathlib leaves). The clopen basis is already lem-weil-pbc-profinite-clopen-basis, a Mathlib leaf. The compact topology of products and fibre powers is already supplied by lem-sfb-finite-quotient-fiber-product. Its statement is used only for that clause, not its inverse-limit proof. The latter is declared as a generic off-unit tool in split_report.tool_uses.

## Not duplicates

No new-node pairs arise. I searched the whole DAG by finite clopen partitions, closed subsets with locally constant functions, finite quotient surjections, the source tags 08ZY/08ZZ/0A2P, and Cech cocycle descent. Blueprint searches for finite valued Cech cocycle descent, clopen, locally constant, and finite quotient found no equivalent blueprint node. The existing finite-quotient-fiber-product result is reused; it does not state descent of a cochain together with its alternating equation.

## Mathlib search results

All new searches ran through msearch.py and their returned records are retained in searches.jsonl and appended verbatim as results in the item. The original node's searches are retained too. A second phrasing (locally constant cocycles on Stone-space nerves) again returned Profinite.exists_locallyConstant and its finite variants. I read CofilteredLimit.lean lines 109–225: these factor one locally constant function on a supplied cofiltered limit; constructing the simultaneous arrow quotient and ensuring its equation on nonliftable tuples is further work. The abstract CategoryTheory.cechComplexFunctor at Sites/SheafCohomology/Cech.lean:65 only constructs a complex. Nobeling's fin_comap_jointlySurjective concerns integer functions on a closed subset of a Boolean cube. The extension search returned Tietze extension theorems, whose target extension hypothesis is not a theorem for arbitrary finite discrete targets and normal ambient spaces. I also read ContinuousMap.exists_finite_approximation_of_mem_nhds_diagonal at Separation/DisjointCover.lean:140–154: this concerns a single supplied function on its domain, not the required quotient-arrow equation. No candidate is an exact match or a one-line specialization of the item. No Mathlib leaf is asserted.

## Review by NK

I read Stacks topology.tex Tags 08ZY (lemma-profinite, its finite clopen decomposition construction), 08ZZ (lemma-profinite-refine-open-covering and proof), and 0A2P (lemma-describe-limits). I also read Bhatt–Scholze Lemma 4.3.9(2)–(4) and its proof on printed page 33, plus current blueprint direct-images proof paragraph (3). Bhatt–Scholze calls the discrete case clear and does not state this finite quotient lemma. Accordingly proof_origin.by is agent: the eight steps give the missing finite clopen construction, not a claimed verbatim Stacks or Bhatt–Scholze theorem. No SGA source is used. There are no new nodes requiring additional source verification.

Step 1 uses the actual statement of lem-sfb-finite-quotient-fiber-product: P is compact Hausdorff totally disconnected. I checked the entire statement: both source maps may be arbitrary continuous maps of such spaces, so it applies repeatedly over S to form P_r and over a point to form ordinary T^r. Coordinate maps give the tuple identifications. The empty map is dealt with before making a nonempty-block choice. The citation quote is exactly the relevant compactness sentence.

Step 2 uses the actual clopen-basis statement, not a finite-partition assertion taken from that node's proof. Both applications of its compact/Hausdorff/totally-disconnected hypotheses hold for T by the item. The subspace/product topology gives rectangles; compactness then supplies finitely many rectangles. Every rectangle has only the given cochain's one constant value on its intersection with P_k.

Step 3 is finite Boolean algebra of those very rectangles: an atom that meets a coordinate clopen lies inside it. A product cell meeting P_k therefore lies inside one selected rectangle. This proves well-definedness of the assigned value, including when several rectangles meet that cell. Values on all other cells are 0, which exists in every abelian group. Continuity follows directly from the finite clopen cells. No separate extension theorem is silently cited.

Step 4 uses only this constructed h, the coordinate topology and pointwise finite sums. The defect locus is closed as well as open because M is discrete, so it is compact. A closed subset of a compact space is compact directly from the open-cover definition by adjoining its open complement. The input cocycle identity says that this locus misses P_{k+1}; thus each of its tuples has two unequal base images.

Step 5 again cites the clopen-basis statement, now applied to S. Hausdorffness gives the open complement of one point. Each chosen separating clopen yields an open rectangle in the two relevant q-coordinates, and compactness of the defect locus selects finitely many of these rectangles. I checked explicitly why the partition by membership in the selected clopens excludes EVERY bad tuple whose base images lie in one block. This is the key argument; it needs neither surjectivity on fibre powers nor a continuity-of-cohomology theorem.

Step 6 is the finite intersection refinement of the two constructed partitions. Only nonempty blocks are retained. Inverse images of clopens along q are clopen. The formula for q_0 is unique because the base partition is disjoint. Its surjectivity uses exactly surjectivity of q and nonemptiness of a chosen base block, and q_0 a = b q is checked on each t. Hence there is no unproved finite-arrow-approximation theorem.

Step 7 defines h_0 by already established cellwise constancy; restricting its domain gives c_0. The original factorization equality is then literally h=c on P_k. Step 8 chooses representatives independently in each quotient block and expands the SAME signed sum. Step 5 applies to those representatives because all images lie in one gamma-block, even if they are different points. This proves every required quotient cocycle equation without changing its signs or degree.

I tested n=1 (three-face equation), a singleton base, an identity map, a finite discrete surjection, the empty surjection, the zero group, and an empty defect locus. For a concrete nonliftable tuple, take T=S={u,v} with identity q and coarsen the base to one block while retaining singleton source blocks. An off-diagonal tuple of blocks has no lift to T_S^2; the final step uses arbitrary representatives in T^2 and does not pretend it lifts. The defect refinement is exactly what can rule out such a tuple or force its signed sum to be zero. This checks the specific potential failure that the statement warns about. All proof steps are below 800 characters, so no step exceeds the long-step threshold. I reviewed B–E against the JSON and sources: statements are self-contained, citations use statements, the proof carries the construction rather than moving the conclusion into new nodes, and no hypothesis is added. The statement and its dependencies are unchanged. There is no target or coefficient-category change.

## Unfinished work

None in this one-level stage-1 split. Its two existing dependencies retain their own library status. Server review_split passed with 0 new nodes; final deliver.py checks are run after this report is written.
