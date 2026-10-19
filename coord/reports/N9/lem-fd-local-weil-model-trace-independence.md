# Stage-1 report: lem-fd-local-weil-model-trace-independence

## Files written

- `dag/nodes/sec-fourier-transform/lem-fd-local-weil-model-trace-independence.json`: statement node, now split into nine proof steps; Mathlib verdict: no match for the geometric point/scalar comparison. Statement, statement dependencies, source and ancestry preserved.
- `citations.json`: 22 step/node entries, with verbatim excerpts of all nine cited node statements.
- `searches.jsonl`: actual msearch results from this session, including two semantic phrasings, LeanSearch, Loogle and source greps. Earlier recorded searches in the item were retained.
- `report.md`: this report.

No new nodes and no new Mathlib leaves. No Lean files, builds or compilers were used; no repository or launcher was modified.

## Attachments

None. Read-only searches of WeilConjectures for the exact blueprint id, localFrobenius, model independence, local-Weil terminology, trace_baseChange and trace_conj found no declaration stating the item. I also read the relevant trace-function portions of `WeilConjectures/WeilSheaf/Stalk.lean`: those define sheaf/complex numerical traces and finite-sum presentations, not the specified rational coefficient-field point comparison. The abstract Mathlib `Action.Iso.conj_ρ` presupposes actions and an equivariant isomorphism; constructing the local operators and proving compatibility with b is the content here, so it is not a one-line specialization giving the item.

## Wanted literature

None for this delivery. The proof is explicitly marked agent-written: the source defines the trace, rather than proving this extracted comparison lemma. No assertion is attributed verbatim to Deligne or Stacks beyond what the cited existing nodes state.

## Discrepancies and corrections

The item statement is mathematically sound with its specified normalization, and was not changed. In particular the point return is `g_X^n ∘ xbar = xbar ∘ g_s^n`, not equality of `g_X^n ∘ xbar` with xbar. The initial statement-only node had no proof; this delivery supplies it. The final-sentence description in source.place should be read together with the unit's numerical trace definition: the main-20261015 definition itself displays the trace formula and names its coefficient categories, while independence is its well-definedness obligation.

The exact main-20261015 chapter and unit, and their DAG records, were read; this item is not the key node and changes neither record. No source error, statement dispute or route replacement was needed. All off-unit theorem citations are generic tools declared in split_report.tool_uses. In particular the integral pullback realization is used only for arbitrary-map composition/scalar coherence, and trace formal laws only for elementary field traces, with no geometric trace-formula result or SGA route.

## Unfinished work

None for the authorized one-level split. Existing dependency nodes retain their own proof obligations; this delivery neither claims their proofs finished nor splits them again.

## Not duplicates

No new nodes. Searched the whole blueprint for Weil objects, local Frobenius, and scalar extension; searched DAG descriptions and inspected `lem-weil-local-frobenius-conjugacy-class` and `lem-trf-local-frobenius-conjugacy`. Both change the lift of a geometric/closed point, whereas this item fixes the point and compares coefficient-field Weil models through a specified b. Neither is an attachment or a replacement for this proof. The existing scalar, cohomology and point-transport lemmas were reused rather than copied into new nodes.

## Review by N9

I read main-20261015 `def-fd-trace-function.md`, its unit and chapter, and the corresponding local-Frobenius and formal-trace-law source files. I also read the current statements of every node cited by every proof step, not merely their titles or dependency lists. As context for these existing comparisons, I read Deligne, Weil II (1.1.3), (1.1.7)-(1.1.11), printed pp. 150-152: rational coefficients, transport of structure and Weil pairs. I read Stacks Tag 099N (`proetale.tex`, lemma-pushforward-Noetherian-case (2),(5)) and Tag 0D6D (`sites-cohomology.tex`, lemma-derived-pullback-composition): these explain completed pullback and ordinary derived composition, but do not themselves assert all integral scalar coherence. The proof correctly cites the separate existing realization lemma for that additional assertion. The node is marked agent-written. No new node has a source to audit.

Step 1 uses exactly the natural point-sections scalar isomorphism and the natural pullback/scalar isomorphism, with the normalization and rationalization of the realization lemma. I checked b's direction: it starts with inverse point-sections comparison, then applies Fib to the pullback/scalar comparison. Its source is the scalar extension of the original point complex; its target is the L-point complex of the extended object. All schemes have ell invertible, and all inputs lie in the specified constructible categories. Integral representatives suffice; no integral representative of the Weil map or a stable lattice is chosen.

Step 2 cites the Weil-pair definition for the intertwining equation, the local-operator definition for the recurrence, and the natural associative composition comparisons. The induction displays both its base and multiplication step. This is elementary composition of those given identities, so it is marked elementary; it does not import a hidden claim about equivariant objects.

Step 3 uses point-transport naturality (2) for arbitrary morphisms, including rational morphisms, and the natural composition comparisons. The written induction on J_r proves naturality of I^[r]; the initial map and inductive extension are explicit. It does not need point transports to be isomorphisms.

Step 4 uses the local-operator definition and the realization lemma for the natural return comparison rho. I checked that rho goes from the s-Frobenius pullback of the point pullback to the point pullback of the X-Frobenius pullback. It is natural because each comparison in its defining composite is natural, including the comparison for equality of scheme maps. Combining this with step 3 and the actual iterated intertwining equation gives the displayed L-local conjugacy before changing coefficients.

Step 5 uses the scalar comparison of that same realization lemma and the Weil-pair/local-operator definitions. I checked its equation types: theta_L^[r] a_r maps T(G_F,r M) to T(M), as does T(theta^[r]). The composition/scalar equation and naturality for theta give the induction exactly as written. It does not assume an unproved uniqueness of comparison maps or equivariance of an arbitrary isomorphism.

Step 6 uses the scalar compatibility explicitly included in point-transport naturality (2), the exact point-sections comparison, and the composition/scalar equation with equality and finite iterations from the realization lemma. I checked the two composites defining rho and the cancellation of the intermediate comparison maps when pasting the n naturality squares. The resulting formula has source D_F(M) tensor L and target D_L(G_L,n(T(M))). Naturality of b for theta^[n] and step 5 then prove the scalar compatibility of the local operator. These are routine finite pastings of existing specified equations, not new comparison theorems hidden as a step.

Step 7 is only associativity and cancellation in the two preceding identities. It gives precisely (b')^{-1} D_L(u) b from the item, not an unspecified conjugating map. Its explicit inverse proves it is an isomorphism. Step 8 uses the actual naturality clause in cohomology-commutes-scalar-extension, not just an abstract vector-space isomorphism. I checked the direction of h_j and of (h'_j)^{-1} H^j(utilde) h_j and that finite-dimensionality is part of the cited local-point definition.

Step 9 uses trace formal laws (1),(3),(4) only on finite-dimensional vector spaces in degree zero, where they are perfect complexes. Clause (4) is the bridge to the ordinary linear trace defined by def-weil-endomorphism-trace; clause (3) allows any commutative coefficient homomorphism, hence the inclusions E -> L and E' -> L. No finite-coefficient complex is declared perfect. The last equality in Qbar follows by composing the fixed field inclusions. The report's citations file copies substantive verbatim formulas/sentences from the statements actually used in these steps.

I checked B1-B10: there are no new nodes, no fabricated search records, no attachment covering only part of the item, and no altered blueprint ancestry. Current msearch hits were read; ordinary LinearMap.trace_conj' (Trace.lean:292) and trace_baseChange (:378) cover linear algebra only, and Action.Iso.conj_ρ (Action/Basic.lean:321) assumes the already-constructed action. They do not remove the point/scalar comparison steps. All source paths and node ids were read in the authorized trees. I checked C1-C8: every non-elementary input is cited by its own statement, uses union equals proof_deps, quotations are literal, and off-unit tool uses are declared. I checked D1-D5: the argument is carried in the item's steps rather than passed to a renamed copy or a clause node. I checked E1-E7: no missing normality, finiteness, flatness or Tor hypothesis is used; no geometric-Frobenius/scheme-Frobenius identification is substituted; the transports and scalar compatibility are given as equations and finite pastings. All non-elementary steps are below 2000 characters and none hides an independent standard lemma.

Small cases checked: n=1 reduces each induction to the original Weil equation and single point-transport square. E=L or E'=L gives the identity scalar comparison. A rank-one constant Weil object with eigenvalue alpha gives the included scalar alpha^n; a comparison to eigenvalue alpha' forces equality by the Weil-pair equation. Zero complexes and zero cohomology groups have trace zero. A shifted complex changes its degree but the assertion is per degree, so no spurious alternating sign appears. Empty X_0 gives no x and a vacuous assertion. A nontrivial Jordan block still satisfies the matrix intertwining equation; no semisimplicity is used. A rational Weil eigenvalue that is not an integral unit is permitted throughout. The equal-scheme-map return, rather than a false fixed-map identity, is used for every n.
