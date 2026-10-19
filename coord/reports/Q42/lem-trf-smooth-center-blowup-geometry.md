# Q42 — lem-trf-smooth-center-blowup-geometry

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-center-blowup-geometry.json`: statement, now split in eight proof steps; no Mathlib match for the complete statement.
- `citations.json`: 27 verbatim statement quotations, one for each step/cited-node pair.
- `searches.jsonl`: the actual search-command records. Earlier Mathlib records in the item are retained.

No new nodes and no new Mathlib leaves. The item statement, statement dependencies, source, creation stamp and inherited blueprint ancestry are unchanged. The item’s blueprint `from.place` was already specific; the whole-blueprint searches found no equivalent statement, so `same_as` remains empty.

## Attachments

None. Searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag and item identifier, and for smooth-center/blowup combinations. No project declaration states all the clauses. In particular the existing general strict-transform/blowup comparison in `Compactification/StrictTransformBlowup.lean` does not assert smoothness of the ambient blowup. It is not an attachment for this item.

## WANTED

None. Every source used is present under `literature/stacks-project/`.

## Findings and changes

The imported statement is true as written. It had no proof. The proof now follows the geometric reduction in more-morphisms.tex Tag 0FUT (`lemma-blowup`), using the existing Tag 0FUE smooth-pair coordinate node. I read the full proof of 0FUT and the preceding Tag 0H1H (`remark-relative-blowup`), as well as divisors.tex Tags 0804, 0805 and 02NS and morphisms.tex Tag 056B. Rather than assume the omitted global Rees-algebra presentation in 0H1H, step 3 computes each chart directly as a subalgebra of a localization and checks injectivity on Laurent monomials. There is no new lemma concealing the smoothness clause.

The coordinate theorem permits codimension zero. I explicitly included that case: the zero ideal has empty blowup, while the unit ideal, corresponding to the empty center, has unchanged blowup. Reduced strict transforms are scheme-theoretic closures, not merely topological closures; step 8 cites the already reviewed reduced-image theorem for this distinction.

The source’s projectivity result is stronger than needed. The proof uses the existing properness node and its finite-type/separated consequences instead of creating a projectivity restatement. Separatedness of the composite is proved by the diagonal factorization, citing closed-immersion base change and writing out composition using the affine quotient definition. No generic permanence theorem was silently assumed.

## Searches and reuse

Before writing, searched all DAG statements and the whole blueprint, including `tools/blueprint_refs.py ancestor lem-trf-smooth-center-blowup-geometry`, `search 'blowup'`, `search 'smooth pair'`, `search 'reduced image'`, `search '01KS'`, and `search 'separated composition'`. Also searched source tags 0FUT and 02NS and phrases involving smooth closed pairs and reduced scheme-theoretic images. Reused `lem-pur-smooth-pair-local-coordinates`, `lem-trf-reduced-scheme-image`, and the existing Nagata blowup interfaces. No new statement is created, so there are no duplicate-node pairs to distinguish.

Ran msearch.py for this item with leanfinder, leansearch, loogle and grep, then a second semantic phrasing. All calls completed and their results were read. The two semantic queries returned smooth-morphism definitions, source-local characterizations and composition instances. None states the blowup theorem. Loogle returned no hits for `"Blowup", "IsSmooth"`; the Mathlib algebraic-geometry grep returned no blowup definitions or results. Exact tools and query texts are in the node and searches.jsonl. No unavailable service was recorded as a negative result.

The two off-unit nonclosed generic tools are declared in `split_report.tool_uses`: smooth-pair coordinates and etale morphisms being smooth. The existing affine-space smoothness interface is already Lean-closed and requires no separate declaration. They are geometric foundations of the local resolution input. They do not substitute another proof for the trace-formula unit’s current contracting-correspondence route. The inherited historical branch and ancestry are retained.

## What could not be finished

Nothing in the requested one-level split remains unfinished. No Lean was written and no compiler or build tool was run.

## Review by Q42

I checked B–E of delivery-errors.md against the actual node statements and source text. There are no new nodes, so B’s standalone-node, source-tag, duplicate and Mathlib-leaf obligations do not arise for a new statement. The item keeps its precise hypotheses. Each of the eight steps is below 2000 characters; the coordinate computation is a single polynomial calculation, not a hidden general comparison lemma.

1. The statement of `def-sbc-closed-immersion-ideal-sheaf` supplies precisely the quasi-coherent ideal of C. `lem-pur-smooth-pair-local-coordinates` applies because both C and P are smooth over the same base Spec Q and C is a closed subscheme of P. It supplies both the scheme-theoretic coordinate inverse image and finite generators, not just a set-theoretic description. Outside C the ideal is the unit ideal. The quotient-ring characterization in `def-weil-closed-immersion` justifies the stated local finite equations and the compactness conditions for the finite-presentation center. No Noetherian assumption is imported.

2. Opened the statement of `thm-nagata-blowup-flat-base-change` together with `def-nagata-blowup-flat-base-change-map`, since the theorem’s statement refers to that constructed comparison. Together they give exactly Bl of the extended ideal = the fiber product with the original blowup. The coordinate map is flat by `def-weil-etale-morphism`; an open immersion induces isomorphisms on local rings. Thus both base-change applications satisfy flatness. The coordinate theorem gives equality of the actual center ideals, so the fiber product uses the correct center.

3. `prop-nagata-affine-blowup-chart-cover` gives the covering by the indicated algebras; `def-nagata-blowup-chart-ring` identifies those as subalgebras of A localized at y_i. The map onto that subalgebra contains every generator, because y_j = y_i t_j. Distinct source monomials have distinct Laurent exponent vectors: beta and alpha are read off first, then e is recovered from the y_i exponent. This proves injectivity without assuming the source’s omitted Rees presentation. For b = 0, presenting the zero ideal by its single generator 0 gives a cover by the empty spectrum of the zero ring. This is an elementary calculation from the cited interfaces.

4. `sbc-lem-affine-space-smooth` states the smoothness of every affine-space projection, with n = 0 allowed. `lem-weil-pbc-etale-scheme-base-change` applies to the coordinate map along each model chart. The statement of `lem-weil-pbc-etale-smooth-zero-dimensional-fibres` explicitly includes smoothness; no use is made of a definition of etale in place of that theorem. `lem-trf-smooth-composition` then supplies the smooth composite over Q. `lem-weil-pbc-smooth-local-on-source` applies to the open covering, including the empty covering when b = 0. No etale descent theorem is needed because the coordinate neighborhoods V are actual open subsets of P.

5. The exact complement-isomorphism clause comes from `thm-nagata-global-blowup-complement`. The restriction and isomorphism clauses in `lem-weil-pbc-smooth-restrict-open-subschemes` transport the assumed smoothness of P to the complement. The covering of P by the coordinate neighborhoods and the complement pulls back to an open covering of P+. Source locality gives the global result and includes empty P and empty C.

6. `lemma-nagata-blowup-proper` requires only a finite-type quasi-coherent ideal, both checked in step 1. `def-weil-proper-morphism` explicitly includes separatedness and finite type. `lem-sfb-finite-type-composition-base-change` clause (1) gives finite type over Q since P has that property. The hypotheses do not assume P proper, and the proof never uses that stronger assumption.

7. The first diagonal is closed by the separatedness just obtained; the second is the base change of P’s closed diagonal. `lem-weil-pbc-closed-immersion-base-change` is exactly the required stability assertion. Composition is checked in the affine quotient description of `def-weil-closed-immersion`, by composing the two surjections; the closed-subset embeddings compose as well. This proves the needed separatedness of P+ over Q, not merely separatedness of its map to P.

8. `def-pc-reduced-scheme` describes reducedness through local rings, so the open X_U inherits it. The complement-isomorphism node makes the strict-transform open isomorphic to X_U. Read `def-nagata-strict-transform`: its closure lives initially in X times_P P+, precisely the ambient scheme used here, and the finite-presentation-center condition was checked. `lem-trf-reduced-scheme-image` states the reducedness of the scheme-theoretic closure of any reduced open, so it applies even if this open is empty or not dense. Closed-immersion base change puts the fiber product inside P+; thus the result agrees with the ambient strict transform. No containment of C in X, equidimensionality, connectedness or maximal-stratum hypothesis is used.

I tested empty P, empty C, C = P, C an open-and-closed component, a Cartier center (b = 1, whose model chart is unchanged affine space), a point in affine space (b > 1), empty X and X contained in C (empty strict transform), X disjoint from C, and a reduced reducible X. The calculation and closure argument cover all these cases. In particular reducedness does not mean irreducibility. There was no statement dispute to repair. All citations.json entries are copied from the actual statements, not from proofs or definition names that do not assert the facts used.
