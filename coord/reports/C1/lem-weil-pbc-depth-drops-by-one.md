# Stage 1 delivery: `lem-weil-pbc-depth-drops-by-one`

## Worker report

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-depth-drops-by-one.json`: five-step independent proof; the item is not a Mathlib leaf because pinned Mathlib has no depth definition.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-rees-ext-regular-sequence.json`: new statement, Mathlib leaf `ModuleCat.exists_isRegular_tfae` (`RingTheory/Depth/Rees.lean:158`).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-ext-annihilator-first-variable.json`: new statement, Mathlib leaf `CategoryTheory.Abelian.Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` (`Algebra/Category/ModuleCat/Ext/Basic.lean:35`).
- This report's worker section.

Lean attachments: none. WANTED: none.

I checked the item against Stacks Algebra Lemma 090R (`lemma-depth-drops-by-one`, lines 17940-17960), Definitions 00LF and 00LI, the depth bound 00LK, the finite local dimension result 00KQ, the Ext sequence 00LU, and Ext annihilation 00LV. The statement agrees with part (1) of 090R. Nakayama makes $Q=M/xM$ nonzero and finite. The existing 00LK and 00KQ nodes make the depths of $M$ and $Q$ finite, and $(x)$ shows $\operatorname{depth}(M)\ge1$. Rees identifies existence of a regular sequence of length $n$ with vanishing of $\operatorname{Ext}^i_R(R/\mathfrak m,-)$ for $i<n$. Because $x$ annihilates the residue field, 00LU and the new 00LV leaf give $0\to A_i\to B_i\to A_{i+1}\to0$, with $A_i=\operatorname{Ext}^i_R(\kappa,M)$ and $B_i=\operatorname{Ext}^i_R(\kappa,Q)$. The first nonzero Ext degree therefore moves from $d=\operatorname{depth}(M)$ to $d-1$, and Rees gives $\operatorname{depth}(Q)=d-1$, including $d=1$.

Source issue: the printed proof of 090R invokes 00LX, whose proof invokes 00LW; the proof of 00LW in turn chooses a nonzerodivisor whose quotient has depth one less. Using those nodes here would make the DAG circular. This item's new proof is marked agent-written, uses the Mathlib Rees theorem directly, and has no edge to 00LW or 00LX. No statement was weakened.

Blueprint searches of imported node titles/statements for depth, Rees, Ext annihilation, and regular sequences found no blueprint node stating the item or either new fact; `blueprint.same_as` is `[]` for all three. Their nearest blueprint ancestor is `lem-weil-pbc-normal-constant-generic`, step 4 of its split, through the flat-local-depth-formula chain recorded in `blueprint.from.via`. The item and both leaves record that reference, and `split_report.blueprint` names the served place. `review_split.py` passes with two new nodes; `check_dag.py` has no cycles and only seven unrelated reachability errors. No local split work remains.

## Review by C1

I read Algebra 090R (`lemma-depth-drops-by-one`), 00LK (`lemma-bound-depth`), 00KQ (`proposition-dimension`), 00LU (`lemma-long-exact-seq-ext`), 00LV (`lemma-annihilate-ext`), and Definitions 00LF/00LI in `literature/stacks-project/algebra.tex`. The item states exactly 090R part (1) for a nonzero finite module and a nonzerodivisor x in the maximal ideal; its extra finite-depth assertion follows from 00LK and 00KQ. The original split followed 090R through 00LX, whose proof uses 00LW, while the concurrent split of 00LW used this item. I sent it back to the worker to remove that hidden source cycle. The final proof is marked agent-written and uses Mathlib's Rees theorem independently of 00LW.

Step 1 applies the Nakayama node to show Q=M/xM is nonzero and writes generators of Q explicitly. Step 2 cites the support-dimension bound and finite local Krull dimension for finite d,e, then uses the regular-sequence and depth definitions for d>=1. Step 3 cites the Ext long exact sequence and new annihilator leaf: x kills k=R/m, so its induced maps on Ext(k,M) vanish; the stated short exact sequences follow by checking kernels and images. Step 4 cites the new Rees leaf at lengths d and d+1. Since a finite supremum of integer regular-sequence lengths is attained, Ext below d vanishes and Ext at d is nonzero. Step 5 uses the short exact sequences to shift the first nonzero Ext degree to d-1, then applies the same Rees equivalence to Q. At d=1 this says Ext^0(k,Q) is nonzero; no negative degree is used. No cited node is used beyond its statement.

I read pinned Mathlib `Mathlib/RingTheory/Depth/Rees.lean` at `ModuleCat.exists_isRegular_tfae` lines 145-166: clauses (2) and (4) give exactly the new Rees leaf under finite M and IM<M; `RingTheory/Regular/RegularSequence.lean` lines 135-148 includes the final nonzero quotient condition of 00LF. I read `Mathlib/Algebra/Category/ModuleCat/Ext/Basic.lean` lines 29-43: `Ext.postcomp_smul_id_eq_zero_of_mem_annihilator` gives the new annihilator leaf. Both are one-declaration Mathlib leaves, with self-contained statements, definition dependencies, file/line locations, and searches. The worker searched the current DAG and the whole imported blueprint for the two facts; neither had an existing equivalent. Their blueprint `from` chains and the item's specific ancestor step are recorded.

I checked M=0 is excluded, x cannot be a unit because x is in m, Q is nonzero by Nakayama, and d=1 works. The worker replaced both the old proof and the stale worker report after my return. `review_split.py` passes with two new leaves; `check_dag.py` has no cycles and only seven unrelated pre-existing reach warnings. Sections A-E of `coord/delivery-errors.md` are satisfied.
