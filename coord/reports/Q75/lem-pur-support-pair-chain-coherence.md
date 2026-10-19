# Worker report: lem-pur-support-pair-chain-coherence

## Files written

- `dag/nodes/sec-smooth-purity/lem-pur-support-pair-chain-coherence.json`: existing item, split into five proof steps; no new nodes.
- `citations.json`: citations for the two existing Mathlib leaf dependencies.
- `report.md`: this report.

## Attachments

None. No finished sorry-free project declaration with the exact item statement was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `/home/ubuntu/weil-newtargets-master/WeilConjectures`.

## WANTED

None.

## What I checked and changed

The imported item is the chain-level refinement used by Step 7 of `thm-pur-with-support-exactness`. I read that parent node, its Step 7 invocation, the item's full statement, and the corresponding Milne *Lectures on Étale Cohomology*, Section 9, Theorem 9.4 (pp. 65--67). The statement has the two site objects, the relation `u(m)∘s=t∘m'`, the adjunction, integer-indexed complexes, and the derived localization exactly as required; no hypothesis or clause was changed.

Step 1 writes the degreewise adjoint and checks the two evaluation-and-restriction composites commute by adjunction naturality and `u(m)∘s=t∘m'`; I checked that the direction of `J(t)` and `J(s)` is correct for contravariant sheaves and that the equation is preserved by differentials. Step 2 uses only the kernel universal property to produce the unique support-kernel map and the three-term diagram morphism. Step 3 takes the adjoint of the degree `-1` map `z`, expands `h-h'=d_Jz+z d_{LI}` after evaluation, and restricts the resulting homotopy to the kernel; this gives simultaneous homotopies on all three components.

For Step 4 I read the existing Mathlib leaf `lem-weil-pbc-bounded-below-injectives-kinjective` and verified that its statement is exactly the needed bounded-below-injective-to-K-injective implication. I also read `lem-weil-pbc-kinjective-hom-derived`, whose statement gives the bijection from homotopy classes of chain maps into a K-injective to derived morphisms and the homotopy-equivalence conclusion for quasi-isomorphisms. These are the only non-elementary proof dependencies, and the exact quotes are recorded in `citations.json`. Step 5 applies the preceding construction to representative comparisons; exactness of `L` follows immediately from its preserving kernels and cokernels, and the cited homotopy-equivalence statement gives the canonical transport between injective representatives.

I tested the construction on the edge cases `V=T` (all support kernels are zero), an initial/empty `V` (the kernel is the full section complex), zero complexes, the identity adjunction and identity pair, and a zero homotopy. In each case the formulas reduce to the expected zero or identity map, and the kernel universal property remains valid. No source or statement error was found, no duplicate/new node was needed, and no SGA source was used.

## Review by Q75

I checked every proof step against the item statement and the source files named above. Steps 1--3 are elementary uses of the adjunction bijection, sheaf functoriality, the kernel universal property, and the displayed chain-homotopy equation; they do not hide an independent lemma. Step 4 uses exactly the two existing Mathlib leaf statements quoted in `citations.json`, with no stronger claim. Step 5 uses the same two statements only for comparison quasi-isomorphisms and transports, while its remaining calculation is the homotopy construction from Steps 1--3. The hypotheses that `L` preserves kernels and cokernels, complexes are bounded below, and `u(m)∘s=t∘m'` are used at the indicated steps. I also checked the small cases listed above and verified that the item remains acyclic/identity-compatible there. The item remains tied to the parent blueprint sentence invoking chain coherence, with no newly created node or cycle.

## What could not be finished

Nothing remains unfinished.
