# lem-weil-pbc-set-cech-nerve-free-resolution

## Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-set-cech-nerve-free-resolution.json`: split the existing statement by the explicit augmented contracting homotopy; no new nodes and no new Mathlib leaves.

## Attachments

None. A search by node ID and by Čech-nerve/free-resolution terms in the slopmaster2 Lean source found no exact declaration. The existing `mathlib_candidate` records the extra-degeneracy route, which is a composite rather than a single exact leaf.

## WANTED

None. The local literature checkout is not materialized on this machine, so I read the published Stacks pages for Tags 01GC, 03AS, and 03AT directly.

## Corrections and limits

The imported `source.place` called Tag 03AT “Sites and Sheaves”; its actual chapter is “Cohomology on Sites.” I corrected that attribution. The statement itself agrees with the setwise computation used in Tag 01GC, with the coefficient ring generalized from $\mathbb Z$ to $R$ by the same basis-level calculation. Nothing remains unfinished in this one-level split.

## Review by E1

I read [Stacks 01GC](https://stacks.math.columbia.edu/tag/01GC), [03AS](https://stacks.math.columbia.edu/tag/03AS), and [03AT](https://stacks.math.columbia.edu/tag/03AT), as well as the existing free-module definition node. Tag 01GC takes a surjection $A=F(U)\to B=G'(U)$ and forms exactly the fibre-power simplicial set in the item; it concludes the free abelian complex has positive homology zero and degree-zero homology free on $B$. Tag 03AS identifies the alternating deletion maps, while 03AT gives the prefixing homotopy for a nonempty set. The item states the $R$-linear version and introduces $A,B,f,R$, the fibre products, their face maps, and the augmentation. No new node was created, so the new-node statement, source, and Mathlib-leaf checks of B are inapplicable.

In step 1, surjectivity supplies one preimage $\sigma(b)$ in each fibre; the cited `def-weil-pbc-free-module` provides extension of a basis formula to an $R$-linear map. The prefix stays in the same fibre because $f\sigma f(a_0)=f(a_0)$. Step 2 checks the face identity on tuples and cancels each pair of terms with opposite signs; it also checks the augmentation in degree one. Step 3 computes the two homotopy identities on basis elements, including degree zero and $\varepsilon h_{-1}=1$. Its cancellation uses only the face maps and the common image of every coordinate, not a hidden simplicial or homology theorem. Step 4 applies these identities to a cycle and to an augmentation-kernel element to obtain exactness. Every step cites only the free-module definition; the rest is written out at basis level. The `proof_deps` is exactly that citation. The cross-unit definition is already a Mathlib leaf, so it does not replace any unit-level proof route.

I checked the hypotheses at the points they are used: surjectivity is needed only to choose $\sigma$ and to make the augmentation split; no finite-fibre, flatness, or commutativity assumption is used. For $B=\varnothing$, surjectivity forces $A=\varnothing$ and all modules are zero. For a singleton $B$, with either one or two preimages, the degree-zero identity reads $[a]-[\sigma(b)]$ as the boundary of $[(\sigma(b),a)]$; the degree-one terms cancel with the same signs written in step 3. The formulas also work over the zero ring and a noncommutative ring because $-1$ is central. I checked the existing DAG and blueprint search before editing; the only related node is the broader `lem-weil-pbc-power-set-complex-contractible` in another unit, while this item's own proof is the direct fibrewise contraction used by 01GC. I corrected the Tag 03AT chapter label and the degree-one/degree-zero cancellation details before delivery.
