1. Files written

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-hypercohomology-e1-pullback-functorial.json`: statement node, split into three proof steps; Mathlib searches found no direct match.
- `dag/nodes/sec-curve-estimates/lem-weil-pbc-cartesian-eilenberg-functorial.json`: statement-only supporting node; Mathlib searches found no match.

2. Attachments

None. No sorry-free slopmaster2 declaration states the item.

3. WANTED:

None. I read `literature/stacks-project/derived.tex` at Definition 015H, Lemma 015I, Lemma 015J, and Remark 015K, and `literature/stacks-project/etale-cohomology.tex` at Lemma 0EZM.

4. Problems found

The imported item was unsplit and had no proof. Its existing statement dependencies define the schemes, inverse image, cohomology pullback, derived global sections, and spectral sequence notation, but they did not state the Cartan--Eilenberg lifting construction. I retained `lem-weil-pbc-cartesian-eilenberg-functorial` as a statement-only node, corrected it to state only the lifted double-complex map and filtered total-complex map, and removed its unsupported E1-page clause. The item has no matching declaration in the Lean source.

5. Incomplete work

No proof is left as Lean code at this stage; the supporting Cartan--Eilenberg node is intentionally unsplit for a later worker.

## Review by G1

I read the item JSON, its blueprint ancestor `prop-weil-pbc-strict-henselization-stalk-formula`, the downstream use in `lem-weil-pbc-etale-cohomology-limit-complex-systems`, and the existing declarations/nodes for `thm-sp-if-e1`, `thm-sp-spectral-object-yields`, inverse-image exactness, inverse-image units, K-injective resolutions, cohomology pullback, derived etale cohomology, inverse-image composition, and pullback functoriality. I read Stacks 015H (the six Cartan--Eilenberg conditions), 015I (existence), 015J (the two spectral sequences), 015K (functoriality), and 0EZM (the complex spectral-sequence comparison), and the item statement agrees with their bounded-below and finite-filtration hypotheses.

Step 1 now explicitly uses the exact inverse-image functor, the termwise unit from `def-weil-pbc-inverse-image`, the lift node's map `F(I_K) -> J_L`, and the fact that both maps are termwise in the double complex, so they preserve the q filtration. `thm-sp-spectral-object-yields` (c) and `thm-sp-if-e1` then give the spectral-sequence morphism. Step 2 uses the row-resolution statement of `thm-sp-if-e1`, bounded-below injectives being K-injective, the K-injective pullback recipe, and the comparison-complex clause of `lem-weil-pbc-cohomology-pullback-functorial`; these say exactly that the graded map is `H^p(u^q)` after `f^*`. Step 3 uses the abutment and associated-graded clauses of `thm-sp-spectral-object-yields`, the derived global-sections definition, unit naturality and composite inverse-image identification, and the sheaf-level identity/composition clauses applied to each `K^q`; the page recursion is the isomorphism `H(E_r) ≅ E_{r+1}` in `def-sp-spectral-sequence`. Every step is non-elementary and cites each fact it uses.

For the supporting node I checked its self-contained hypotheses, inline 015H conditions, 015I/015K source, statement-only form, Mathlib searches, created metadata, and absence of duplicate statements in the DAG, blueprint, or Lean source. I tested identity, zero, and one-degree complexes. I also checked every `citations.json` quote verbatim against the cited node statement. The repair specifically addresses the returned C4 points: the global-section map is constructed, the E1 clause was removed from the supporting node, and composition is argued directly for complexes before using page recursion.
