1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-etale-relation-restriction-quotient.json`: split, with six proof steps; statement unchanged.
- `citations.json`: thirteen entries covering every node cited by the six steps, each with a verbatim statement excerpt.
- `searches.jsonl`: actual logged Mathlib searches, retained with their results. Existing imported search records are preserved; the current semantic search and the valid `AlgebraicGeometry` grep give the no-exact-match conclusion.

New nodes: 0. New Mathlib leaves: 0.

2. Attachments: none. Searching `WeilConjectures/` in slopmaster2 by the exact blueprint tag and by relation restriction, quotient sheaf, and quotient/injective terms found no declaration stating this item. The read-only upstream master was also checked as reference, not treated as a finished proof.

3. WANTED: none.

4. Audit and corrections: the statement is sound and is unchanged. The original Groupoids Tag 045Z is correct: its label is `lemma-quotient-pre-equivalence-relation-restrict`, and it states the quotient injectivity and covering-isomorphism assertion. Spaces Tag 02WT, label `lemma-pullback-etale-equivalence-relation`, proves the etale restriction assertion. Groupoids Tag 02VH gives the corresponding groupoid version. The item's existing `source` metadata is preserved. The earlier draft's assertion that 045Z was the wrong tag was mistaken and is withdrawn.

The first delivery draft introduced `lem-trf-fppf-quotient-relation-restriction` and applied it to prove the item's quotient clauses. I removed that unmerged draft node from this replacement delivery: its content belongs in the item's proof (D1/D2). Steps 3–6 now give the presheaf calculation, sheaf-local injectivity, local lifts, and gluing directly. Step 2 now cites the existing etale composition statement in addition to etale base change; base change alone did not justify the composite.

5. Unfinished: none. Only stage 1 was performed: no Lean source was written and no compiler, Lake, or build command was run.

## Review by Q74

I read `coord/brief-stage1.md`, `stages/1-dag.md`, the three levels in `SETUP.md`, `coord/delivery-errors.md` B–E, `GOAL.md`, and `coord/dag-sync.md`. I read the item's chapter and `sk-i-curve-zero` unit, the blueprint ancestor metadata and current local-term blueprint, and the parent `lem-trf-etale-relation-quotient`. This item remains the parent's atlas-refinement input; it does not invoke the parent's representability theorem, so the quotient theorem is not being used circularly. Blueprint searches for equivalence relations and quotient/sheafification statements found no blueprint node stating this restriction result in another form; `same_as` is empty. No unit or chapter record is changed.

I checked the argument against Spaces `lemma-pullback-etale-equivalence-relation` (02WT, statement and proof) and Groupoids `lemma-quotient-pre-equivalence-relation-restrict` (045Z, statement and full proof), including the covering clause and its groupoid counterpart `lemma-quotient-groupoid-restrict` (02VH). I read Sites `lemma-sections-sheafification` (00WK) and `theorem-plus` (00WB), which supply precisely the generic local facts used in the quotient proof. No SGA source is used.

For Step 1 I opened `def-pc-fibre-product`: its universal property gives the natural identification of a point of the restricted relation with a triple. Pulling back the original set equivalence relation gives reflexivity, symmetry, transitivity and uniqueness with fixed endpoints. This is an elementary verification, not an invocation of a new relation theorem.

For Step 2 I opened both cited statements. `lem-weil-pbc-etale-scheme-base-change` says that an arbitrary scheme base change of an etale map is etale, and clause (2) of `lem-weil-pbc-etale-composition-cancellation` says the composite of two etale maps is etale. The proof names the intermediate schemes A and B and specifies which arrow is a base change of g and which is a base change of s or t. All four original maps have the stated etale hypotheses; no separation, finiteness or surjectivity is required here.

For Step 3 I reread `def-pc-fibre-product` and `def-weil-pbc-sheafification`. Equality of equivalence classes of the g-images is witnessed by an R-arrow, which together with the two chosen U'-points gives an R'-arrow. This proves the presheaf injection directly. The sheafification definition is used only for its actual universal property, to define alpha and its unit equation; it is not cited for local lifting or local equality.

For Step 4 I opened `lem-weil-pbc-site-sheafification-sections-local`: its statement supplies both local representatives of a section of a set-presheaf sheafification and local equality of presheaf elements with equal sheafified images. I also opened clause (1) of `def-weil-pbc-sites-and-cohomology`, which gives covering base change, composition and the sheaf equalizer condition. Those axioms yield a common refinement for the two representatives and compose subsequent refinements. Applying the local-equality assertion to P, then the already proved presheaf injection, gives equality in F' on a covering and hence globally. The site and set universes are those of the size-bounded big fppf site; the local theorem's universe is chosen to contain that site data. No abelian-group sheaf result is substituted for a set-valued one.

For Step 5 I opened all five cited statements. `def-weil-etale-morphism` provides flatness and local finite presentation; `def-pc-fppf-site` defines coverings by these two conditions and joint surjectivity. `lem-weil-pbc-etale-covering-base-change` preserves both etaleness and joint surjectivity under the specified pullback. The local-representative statement supplies a map a_i representing a quotient class; the projection b_i from its pullback along g supplies the required lift, with the equality g b_i = a_i pr explicit. The site composition axiom makes these local lifts a covering of T. This argument uses scheme-surjectivity only to produce a covering, never to claim U'(T) -> U(T) is surjective.

For Step 6 I reread the sheaf equalizer clause. Step 4 applied on each overlap makes the local lifts agree; F' then glues them uniquely, and separation of F checks their image. Uniqueness proves naturality of the inverse under every restriction. This is a direct elementary gluing calculation after Steps 4–5.

Both off-unit generic tools are declared in `split_report.tool_uses`: the set-sheafification local statement and clause (1) of the site/sheaf definition. Other geometric inputs are already Mathlib leaves. Every node cited by a proof step is unmerged and its statement gives exactly the quoted ingredient (C1/C4). The proof dependency list is exactly the union of the step citations. All six steps are below 2000 characters; none hides a comparison lemma or a separate standard argument. There are no new statements needing a duplicate check or Mathlib-leaf decision.

I tested g = identity (identity quotient), a proper open inclusion with the diagonal relation (injective quotient map need not be an isomorphism), U' empty with U nonempty (the injectivity assertion still holds, and the surjective conclusion is not invoked), U empty (then U' is empty), and a surjective non-injective etale atlas U disjoint-union U -> U (the cross-sheet arrows in R' restore the original quotient). For g:Spec(C) -> Spec(R) with the diagonal relation, there need not be an R-rational lift before covering: the pullback cover in Step 5 is essential and supplies it. These checks confirm the stated hypotheses rather than adding any. No conclusion is weakened.
