Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-derived-etale-cohomology-limit.json`: repaired proof; Mathlib search remains no match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-etale-cohomology-limit-complex-systems.json`: new statement-only node for Stacks 0EZM; Mathlib search found no match.
- `citations.json`: verbatim excerpts of every cited statement, by step.

Attachments:

- None. No declaration in the read-only Lean source states the new 0EZM node or the item exactly.

WANTED:

- None. The Stacks source was read at `/home/ubuntu/c1-stacks-review/etale-cohomology.tex` (the literature tree on this machine has no checked-out Stacks source).

What was wrong or incomplete:

- The previous proof asserted that the inverse image of an injective complex computed derived global sections. That is false: inverse image need not preserve injective or Gamma-acyclic sheaves. Its degree-zero continuity comparison therefore did not prove the displayed higher-degree isomorphism. I replaced it with the full complex-system lemma 0EZM and removed the obsolete injective, 09YQ, and filtered-colimit citations. The item's mathematical statement is unchanged; its citation for $K_i$ and $K_Y$ now names the derived inverse-image definition rather than the sheaf-level one.

What could not be finished:

- Nothing.

## Review by M1

I read Stacks Etale Cohomology, Lemma 0GIT (lines 7852-7874) and its input Lemma 0EZM (lines 7783-7823), including the hypotheses and proofs. The item has exactly 0GIT's base scheme, qcqs terms, affine transitions, derived pullbacks, and bounded-below object; neither result requires torsion or finite coefficients. The new node states 0EZM for compatible complexes on the system with one common lower bound, and its conclusion is hypercohomology in every degree. Its statement does not assume acyclicity. I checked its small cases: a constant identity system gives the identity map, a zero complex gives zero groups, and a complex concentrated in degree zero specializes to the all-degree sheaf continuity theorem 09YQ. The Stacks proof of 0EZM uses 09YQ for every bidegree $H^t(X_i,F_i^s)$, followed by a bounded-below spectral-sequence comparison; the common lower bound makes the number of contributing columns finite in each total degree. This is the content intentionally left for the new unsplit node, not an unstated argument inside the item.

For Step 1, I opened `def-weil-abstract-derived-category`: its statement defines $D$ as the localization of complexes by quasi-isomorphisms. I opened `def-weil-pbc-bounded-derived-subcategories`: it says $K\in D^+$ has zero cohomology far below. These two cited clauses justify choosing a complex and a bound. I wrote the good truncation at that bound explicitly: the coker in degree $a$, zero below, and the identity above give the same cohomology, hence a quasi-isomorphism. This is a direct calculation, and it never uses injective terms. For Step 2, `def-weil-pbc-derived-inverse-image` explicitly says termwise pullback represents the derived inverse image; the sheaf-level inverse-image definition does not say that. `lem-weil-pbc-inverse-image-composition` supplies the canonical comparison for the two successive pullbacks, and `lem-weil-pbc-colimit-constant-connected-diagram` says the colimit of the resulting identity diagram is its common value. I checked the diagrams after pullback to $Y$: each term is the same $F_Y^r$, with the composition isomorphisms making the transition maps identities. Since inverse image sends zero to zero, the bound $a$ is shared by every $F_i^\bullet$.

For Step 3, I opened the new 0EZM node and checked that its statement gives exactly the all-degree complex cohomology comparison for the system just constructed, including the uniform bound and affine-transition hypotheses. I opened `def-weil-pbc-etale-cohomology`: its complex clause defines $H^n$ through derived global sections and a K-injective resolution, which is the meaning used in the step. Step 4 only substitutes the representing complexes and identifies the canonical maps, so needs no further lemma. The quotes in `citations.json` are verbatim parts of these statements. I searched the DAG and blueprint for 0EZM and the complex-system result before creating its node; I also searched the read-only Lean source and Mathlib with LeanFinder, Loogle and source search. LeanSearch returned HTTP 500, recorded on the new node. The 0EZM node is in the item's unit, while the only off-unit generic theorem tools still used are inverse-image composition and the connected-diagram colimit; `split_report.tool_uses` lists those two. I rechecked each used statement against C1 and C4, and repaired the E3 failure by removing every claim that global sections of the pulled-back terms compute derived cohomology.
