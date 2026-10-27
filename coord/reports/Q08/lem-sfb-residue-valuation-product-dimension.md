# Stage-1 delivery: lem-sfb-residue-valuation-product-dimension

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-residue-valuation-product-dimension.json`: split item, four steps, unchanged statement, no Mathlib match.
- `dag/nodes/sec-six-functors-basics/lem-sfb-rational-residue-distinct-order-basis.json`: statement, unsplit; no Mathlib match after two semantic phrasings, LeanSearch, two Loogle patterns and source grep. This is the only new node; there are no new Mathlib leaves.
- `citations.json`: one entry for every step/node citation, quoting the entire verbatim statement for reliable checking.
- `searches.jsonl`: genuine searches logged by the required msearch command; previous item searches retained, new searches copied exactly from this log.
- `report.md`: report and Q08 self-review.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag, residue-valuation product terminology, product subspaces, distinct valuations and valuation bases, including its LinearAlgebra and RingTheory directories. No project declaration states every clause. Existing Mathlib declarations concerning lattice ranks, ordinary bases, quotient bases and dimensions of sums are not attachments and are not matches.

## Wanted literature

WANTED: Morrison, *GIT constructions of moduli spaces of stable curves and maps*, arXiv:0810.2340, Section 2.4, Theorem 5, printed p.10, for the inherited Clifford-bound motivation of lem-sfb-residue-valuation-product-dimension. The named local PDF remains absent and is not listed as obtained. I did not fetch it or claim to read it. This delivery proves the standalone auxiliary by an explicitly agent-written valuation argument and uses the local Stacks source instead; it makes no claim that Morrison states or proves this auxiliary.

## Problems checked and changes

The imported auxiliary statement is correct as written. No STATEMENT-DISPUTED change is needed. Its source already says the valuation lemma is an agent auxiliary rather than a separately stated theorem of Morrison; I preserved that history, while the new proof_origin identifies the actual local Stacks material and the agent argument. No statement, chapter or unit route was changed. The existing node had no proof, no lean attachment and no repair note. The sandbox had no previous split or search log. Existing original item search records were preserved.

The one non-elementary subclaim is existence of a basis of distinct orders. It is not a clause of the item's product-dimension conclusion: it concerns one subspace, no multiplication of two subspaces and no product bound. It is not a two-line consequence of the current cited statements. It is therefore a new statement-only node, with its proof kept here as handoff material. Conversely, choosing a monotone chain of products, expanding two finite sums, and iterating unequal-valuation addition are short calculations and were not made into new nodes.

The inherited blueprint.from.node is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-residue-valuation-product-dimension` confirms that the nearest imported ancestor is None. I preserved that inherited value and via chain and prepended the item for the new node. I read the current latest blueprint's `sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.md` and `.proof.md` (frontmatter id det-thm-sf-ctf-stability-direct-images). This deep auxiliary supports the inherited alteration/plurinodal-input route to clause (3), not a replacement of the unit route. The item is not the key unit node, so no realized fields were changed. Searches of the entire imported blueprint for `Clifford`, `products of subspaces`, `product subspace`, `valuation basis`, `basis valuation`, `distinct valuations`, `orders of vanishing`, `vanishing orders`, `adapted basis`, and `one-dimensional residue` found no duplicate. Broader `valuation`, `subspace`, `product` and `residue field` searches were inspected along with targeted searches of DAG statement text. Incidental matches to evaluation or unrelated adic lattices do not state this auxiliary.

## Proof handoff for the new statement-only node

This proof is agent-written, using the normalized valuation of Stacks Tag 00IE (algebra-definition-value-group), the elementary valuation inequality of Tag 00IF (algebra-lemma-properties-valuation) and the unit-times-uniformizer factorization of Tag 00PD (algebra-lemma-characterize-dvr). All three places were read in the local algebra.tex. None of these tags itself asserts the new basis theorem.

Let $t$ generate the maximal ideal, and put $\nu(0)=+\infty$. Every element of $k^\times$ is a unit of $R$, so has value zero. Induct on $d=\dim_k U$. For $d=0$ use the empty basis. For $d>0$, choose any basis $e_1,\ldots,e_d$ and let $N=\min_i\nu(e_i)$. The valuation inequality and zero values of nonzero scalars show that every nonzero $x\in U$ has $\nu(x)\geq N$. One chosen $e_i$ has order $N$, so the linear map
$$\lambda:U\longrightarrow k,\qquad x\longmapsto\operatorname{res}(t^{-N}x),$$
where residue is identified with $k$ by the given isomorphism, is well defined and nonzero. Indeed $t^{-N}x\in R$ for all $x\in U$, and an element of order zero is a unit and has nonzero residue. Choose $u$ with $\lambda(u)\ne0$. Let $U'=\ker\lambda$. For any $x\in U$, the vector $x-\lambda(x)\lambda(u)^{-1}u$ lies in $U'$, and $ku\cap U'=0$, so $U=ku\oplus U'$ and $\dim U'=d-1$. Every nonzero vector in $U'$ has order strictly greater than $N$, because $t^{-N}x$ has zero residue. By induction choose a basis of $U'$ with distinct increasing orders; adjoining $u$ first gives the required basis of $U$. This proof applies to all coefficient fields, uses only finite-dimensional linear algebra, allows negative $N$ in the fraction field, and uses neither completeness nor an algebraic closure. A future split of this new node must cite the supporting nodes for its valuation facts; this delivery does not split the child.

## Review by Q08

I read delivery-errors B through E, the worker brief, the stage-1 contract, GOAL.md, the three levels in SETUP.md, the item's chapter and unit records, and the latest blueprint direct-image statement and proof. For the item and the new auxiliary I read Stacks algebra.tex at Tag 00IE (the group $K^\times/R^\times$ and the integer normalization), Tag 00IF (the multiplicativity and sum inequality), and Tag 00PD (equivalence of DVR descriptions and unique uniformizer factorization). I have not treated an absent Morrison PDF as a read source.

For step 1 I read the whole new auxiliary statement: it gives precisely a basis with increasing normalized orders for each finite subspace under the item's identical fraction-field, subfield and residue-isomorphism hypotheses. I verified it does not require algebraic closedness, completeness or finite transcendence degree. Its zero-space convention makes it meaningful independently; the item uses it only for nonzero spaces. This is the only non-elementary new input.

For step 2 I read def-weil-finite-dimensional-subspace: it defines finite dimension by a finite spanning family. The double-sum expansion proves the rs products span exactly P, so that citation says exactly what is used. No tensor-image theorem or unexplained identification is needed.

For step 3 I read lem-sc-dvr-valuation-arithmetic: its statement explicitly gives $\nu(ab)=\nu(a)+\nu(b)$ for nonzero field elements. All basis vectors and all products are nonzero because K is a field. Adding a fixed integer preserves strict order, so the displayed chain has exactly r+s-1 terms. There is no assertion that all rs orders are distinct; collisions such as $0+1=1+0$ are harmless. The step does not import a sumset theorem.

For step 4 I reopened def-sc-discrete-valuation-ring, lem-sc-dvr-valuation-arithmetic and def-weil-vector-space-dimension. The first includes the valuation-ring/value-group characterization (read against 00IE), so a unit has zero class in $K^\times/R^\times$. The second explicitly provides equality with the minimum for sums of unequal orders. Its formula is meaningful as stated on nonzero elements; equivalently, if $a+b=0$, then $a=-b$ has the same order, so the unequal-order situation cannot have zero sum. Iteration from the largest-order summand downward is finite, and each partial sum has the least order already used. Thus coefficient terms cannot cancel. The dimension node defines dimension as basis size, and extending a finite independent family to a basis gives the stated inequality. These are the actual statements quoted in citations.json, not conclusions borrowed from their proofs. The text is a short explicit scalar/unit calculation and a finite induction on the number of terms, rather than a hidden valuation-basis theorem.

I checked the small cases: d=0 in the child gives the empty basis; r=s=1 in the item gives one nonzero product; if just one dimension equals 1 the chain has one segment and gives the exact dimension of multiplication by a nonzero scalar. Negative orders, positive characteristic, and finite k work unchanged. For sharpness take $R=k[t]_{(t)}$, $K=k(t)$, $V=\langle1,t,\ldots,t^{r-1}\rangle$ and $W=\langle1,t,\ldots,t^{s-1}\rangle$; then $P$ has dimension r+s-1. The rational-residue condition cannot be omitted: for a proper finite extension $L/k$ of degree n>1, take $R=L[t]_{(t)}$, $K=L(t)$, $V=W=L$. The product span has dimension n<2n-1, and the basis-order claim also fails because every nonzero element of L has order zero. This tests exactly the hypothesis used in the child's residue functional, rather than adding a hypothesis to repair the theorem.

I checked Mathlib candidates in their actual source: IsLocalRing.basisQuotient (Quotient.lean:84) concerns a finite free algebra and its quotient over a residue field, not an arbitrary scalar-field subspace of a fraction field; Module.Basis.exists_basis (VectorSpace.lean:176) gives no valuation condition; Submodule.exists_smith_normal_form_of_rank_eq (PID.lean:581) concerns R-module bases with equal R-rank, not a k-basis with distinct orders; Submodule.IsLattice.finrank_of_pi (Lattice.lean:191) gives a lattice's R-rank; LinearMap.finrank_le_of_isSMulRegular (StrongRankCondition.lean:565) bounds dimensions under scalar multiplication and does not imply the r+s-1 estimate. Semantic rephrasings returned these same distinctions. No unavailable search was recorded as a negative result, and no unrun search was added.

I checked every proof step is shorter than 2000 characters (282, 290, 314, 932 initially; total 1818). The short assembly retains the product argument instead of delegating the item's conclusion to a renamed lemma. There is no dependency from the new child back to the item. All cited definitions and the arithmetic leaf already exist and are unmerged. No off-unit statement tool is needed by the item's proof: its one new child inherits the unit, the arithmetic input is a Mathlib leaf, and the others are definitions. The source references explicitly distinguish what Stacks states from the agent-written arguments. All changes are inside the authorized sandbox; no Lean, builds, compiler, repository git commands, launcher edits or other agents were used.

## Not duplicates

lem-sfb-rational-residue-distinct-order-basis vs def-sc-discrete-valuation-ring: the existing node defines DVRs and uniformizers, and does not assert a basis theorem for scalar subspaces. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-sc-dvr-nonnegative-valuation-in-ring: the existing node detects ring membership from nonnegative order, not a basis or any k-dimension statement. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-sc-dvr-tensor-surjective-negative-valuation: the existing node deduces a negative-order element from a tensor-surjectivity hypothesis, and does not construct a basis in an arbitrary finite subspace. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-sc-dvr-valuation-arithmetic: the existing node states multiplicativity, powers and unequal-order addition, not existence of bases of distinct orders. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-sc-dvr-valuation-ring-characterization: the existing node states nonnegativity on the ring and values of a uniformizer and its inverse, not a finite-subspace basis. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-weil-l-adic-extension-integers-dvr-factorization: the existing node factors each nonzero fraction as a unit times an integer power, not a basis of a finite k-subspace. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-weil-l-adic-extension-integers-dvr: the existing node constructs the integers of a finite Q_l-extension and their valuation structure; its scalar field has different characteristic from its residue field and it does not assert the rational-residue basis result. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs def-weil-pbc-cohen-ring: the existing node defines complete DVRs of mixed-characteristic Cohen type, and asserts no basis theorem. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs def-trf-totally-ordered-abelian-group: the existing node defines ordered abelian groups and proves no valuation-basis statement. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-trf-ordered-group-prime-ideal-convex-correspondence: the existing node is an ordered-group prime-ideal classification without a field, rational residue, or vector subspace. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-trf-separably-closed-value-group-divisible: the existing node states divisibility of the value group over a separably closed field, not a discrete valuation or a finite-subspace basis. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-trf-valuation-prime-convex-correspondence: the existing node classifies prime ideals by convex subgroups of the value group, not bases or k-linear filtrations. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

lem-sfb-rational-residue-distinct-order-basis vs lem-trf-valuation-ring-ideal-correspondence: the existing node classifies ring ideals by positive-cone ideals of the value group, not arbitrary k-subspaces with a rational residue map. The new node instead supplies increasing-order k-bases under the rational-residue hypothesis.

## Unfinished work

None for this one-level split. The new auxiliary intentionally remains statement-only and unsplit, as required; its complete handoff argument is above. Delivery validation and its final commit are reported by deliver.py.
