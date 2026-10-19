# Worker report: lem-asd-proper-open-refinement-adjoint-projection

## Files written

- `dag/nodes/sec-smooth-purity/lem-asd-proper-open-refinement-adjoint-projection.json`: repaired Step 3 and added the new K-injective counit dependency.
- `dag/nodes/sec-smooth-purity/lem-asd-derived-counit-k-injective-termwise.json`: statement-only helper node; Mathlib searches found only generic derived-counit declarations, so verdict is no exact match.
- `citations.json`: verbatim statement quotes for every cited node at every step.

## Attachments

None. I searched the slopmaster2 `WeilConjectures/` tree for the item id, its key phrases, and the relevant proper/open declarations; no sorry-free project declaration states this item exactly.

## WANTED

None.

## Not duplicates

- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-kinjective-pullback-abutment`: the existing node concerns a pullback-abutment comparison for K-injective pullbacks; the new node identifies the derived inverse-image/direct-image counit with the ordinary counit.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-kinjective-unit-leray`: the existing node gives a Leray/unit comparison for K-injectives; the new node gives the counit representative for one morphism.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-qcqs-higher-direct-image`: the existing node bounds higher direct images for qcqs maps; the new node is an adjunction-map normalization and has no cohomological bound.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-right-adjoint-preserves-kinjective`: the existing node proves that a right adjoint preserves K-injectives; the new node uses K-injectivity to identify the derived counit map.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-termwise-adjunction-homotopy`: the existing node gives the homotopy-category adjunction; the new node descends its counit to the derived category and states the K-injective representative.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-exc-proetale-derived-open-restriction`: the existing node is a pro-etale open-restriction result; the new node is for small etale constant-module inverse image/direct image and applies to arbitrary scheme maps.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-trf-proetale-unit-leray-chain-formula`: the existing node computes a pro-etale Leray unit chain formula in its specialized coefficient setting; the new node computes the ordinary counit in the etale module setting.

- `lem-asd-derived-counit-k-injective-termwise` vs `lem-weil-pbc-derived-exchange-termwise`: the existing node states compatibility of an underived exchange map with the derived exchange after arbitrary K-injective replacements; the new node states the derived adjunction counit itself is represented by the ordinary counit on a K-injective complex.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-sfb-derived-composition-adjunction-normalization`: the existing node normalizes a conjugate of a composition of derived right adjoints; the new node is the single inverse-image/direct-image counit representative needed here.
- `lem-asd-derived-counit-k-injective-termwise` vs `lem-trf-local-term-clopen-idempotent`: that node proves a clopen idempotent and an integration formula in a proper pro-etale setting; the new node is the general etale K-injective counit calculation.

## What was wrong or incomplete

The returned delivery identified three errors in the old Step 3. It incorrectly called the first map an inclusion of the section component, although $p^*j_{2!}J$ has both the $W$ and complementary pieces. It also said the counit had zero target on $W^c$, although the chosen $I$ is only acyclic there. Finally, it asserted the identity with $\pi_{p,M}$ without proving it and cited `def-kun-unbounded-exchange` for a representative formula that its statement does not contain.

I removed those claims. The repaired step first uses naturality of the ordinary counit to factor the representative composite through the underived map $\psi_J:p^*j_{2!}J\to j_{1!}J$. It then restricts to $W=p^{-1}(j_2(U))$: the proper-support pullback clause and the proper/open support-composition identification give $j_2^{-1}p_*j_{1!}M=q_*s_*M$, so the restriction of $\psi_M$ is the ordinary counit $q^*q_*s_*M\to s_*M$. Since $qs=1_U$, the clopen sheaf decomposition makes this identity on $s(U)$ and zero on the complementary component, which is exactly $\pi_{p,M}$. The inverse base-change map $\beta^{-1}$ is used only through the stated module base-change isomorphism.

The new helper node is statement-only, self-contained, and strictly smaller than the item. I searched the whole DAG and blueprint for its K-injective counit statement and found no duplicate. Its required LeanFinder, Loogle, grep, and LeanSearch commands were run on 2026-10-17; the generic Mathlib derived-counit hits do not state the sheaf/K-injective representative, and Loogle reported its `KInjective` identifier unavailable. I tested the repaired identity on the identity refinement, an empty complement, an extra clopen component, the zero ring, and complexes concentrated in one degree.

## Review by N0

I read Stacks Tag 0F7B (lemma-shriek-proper-and-open, case (b)), the imported blueprint ancestor `prop-asd-smooth-base-change`, and every cited node statement. Steps 1 and 2 remain as previously checked: Step 1 constructs $W$, its open section and clopen decomposition using the fibre-product, open-section, proper-base-change, and finite-clopen sheaf statements, then applies the stated extension-by-zero base-change isomorphism; Step 2 applies exactness degreewise to arbitrary unbounded complexes.

For repaired Step 3, `lem-amb-unbounded-proper-open-interchange` supplies exactly the normalized K-injective representative $j_{2!}J\cong p_*j_{1!}J\to p_*I$. The new `lem-asd-derived-counit-k-injective-termwise` statement supplies the missing fact about the derived counit on $QI$. The module inverse-image node supplies the exact adjunction and its ordinary counit. The proper-support composition node supplies both the proper/open specializations and the pullback comparison for the base change $W\to U$; its hypotheses hold because $p$ is proper and $j_2$ is an open immersion. The open-section and clopen-product nodes say that $s(U)$ is a clopen component and that a sheaf morphism is determined componentwise. The extension-by-zero base-change map and its module isomorphism supply the direction and invertibility of $\beta^{-1}$ used in the identification.

I checked all hypotheses: $A$ is finite, all schemes are Noetherian, $p$ is proper, both $j_i$ are open, and only the original commutativity $pj_1=j_2$ is used; the displayed refinement square is never treated as cartesian. The corrected calculation also handles $U=\varnothing$, $W=s(U)$, a nonempty complementary component, the identity map, the zero ring, and degree-zero complexes. Every quote in `citations.json` is an exact substring of its cited node statement, and `proof_deps` is the union of all step uses.
