# Delivery report

1. Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-filtered-category-directed-cofinal.json`: statement split into three proof steps; status `split`.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-filtered-category-exists-directed-final.json`: statement node, Mathlib leaf; verdict `CategoryTheory.IsFiltered.exists_directed` exact match.
- `citations.json`: verbatim quotes for every cited node in every proof step.

2. Attachments:

- None. No sorry-free slopmaster2 declaration carries the item tag or states this result exactly.

3. WANTED:

- `literature/stacks-project/categories.tex`, Tag 0032, line 2710, for direct source-text verification; this checkout contains the tag index and imported source locators but not the TeX file.

4. Problems found:

- The imported item had no proof steps and its recorded Mathlib search was only a candidate search. I supplied the missing argument using one directed index and the opposite initial functor.
- The existing `lem-weil-pbc-cofiltered-limit-directed-reindex` node only states a limit conclusion and does not guarantee an index working for all diagrams, so it cannot justify the colimit clause or the shared-index requirement. I therefore added the smaller existence leaf and cited the reviewed generic colimit and limit transport leaves.
- No statement was changed. Small cases checked: a one-object filtered category gives a singleton directed set and both clauses reduce to the original (co)limit; a directed poset with its identity functor gives the usual directed (co)limit descriptions.

5. Unfinished:

- Nothing for this item.

## Review by K1

I read the imported item node, its blueprint ancestry (`lemma-weil-pbc-proper-strict-henselian-h0`), the unit `sk-thm-iff`, and the reviewed source-derived nodes `lem-weil-pbc-initial-functor-cofiltered-criterion` and `lem-weil-pbc-initial-functor-limit`. The item statement agrees with Categories Lemma Tag 0032: a small filtered category is represented by one nonempty directed system, and that same system computes colimits of covariant diagrams and limits of contravariant diagrams. The new existence leaf is the exact directed-index conclusion of the same Tag 0032 result.

Step 1 cites the new leaf, whose statement explicitly supplies a nonempty directed set and a final functor `F : A -> J`; functoriality gives the identity and composition equations for the displayed transition maps. The cited statement also makes clear that the choice is independent of the target category and diagram.

Step 2 applies the existing `lem-weil-pbc-initial-functor-cofiltered-criterion` to `F.op : A.op -> J.op`. Its statement explicitly says that for every functor out of `B.op`, colimits over `B.op` and over `A.op` after precomposition are canonically isomorphic. Taking `B = J` and identifying `A.op.op` with `A` gives clause (1), with the same `A` from step 1.

Step 3 applies the existing `lem-weil-pbc-initial-functor-limit` to the same `F.op`, now viewed as an initial functor into `J.op`. Its clause (a) explicitly says a cone is limiting exactly when its restriction is limiting, so it gives clause (2) for the same directed index. Every citation is recorded verbatim in `citations.json`, and `proof_deps` is the union of the three step citation lists.

For the new Mathlib leaf I searched by natural language, declaration pattern, and source grep. `CategoryTheory.IsFiltered.exists_directed` at `Mathlib/CategoryTheory/Presentable/Directed.lean:544` states exactly the required nonempty directed partial order and final functor. I also checked the source locations recorded by both transport leaves (`Final.colimitIso` and `Initial.isLimitWhiskerEquiv`) rather than relying on names alone. No duplicate statement was found in the DAG or blueprint, and no Lean declaration in slopmaster2 states this item. The singleton and directed-poset edge cases are consistent with the construction.
