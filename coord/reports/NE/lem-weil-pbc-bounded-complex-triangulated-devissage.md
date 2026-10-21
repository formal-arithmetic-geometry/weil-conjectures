# Stage-1 report: lem-weil-pbc-bounded-complex-triangulated-devissage

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-bounded-complex-triangulated-devissage.json`: item, statement, split with five proof steps; no Mathlib match.
- `citations.json`: six verbatim statement quotations covering every step-node citation.
- `searches.jsonl`: actual search-command results for the item; two semantic phrasings, LeanSearch, two Loogle patterns and two grep patterns.
- `report.md`: this report. No new nodes or Mathlib leaves.

## Attachments

None. Searched the project Lean tree for the exact blueprint tag and for bounded/triangulated/term and stupid-truncation notions. The closest declarations, `DerivedCategory.prop_of_isGE_of_isLE`, `DerivedCategory.prop_of_bounded`, and their degreewise variants in `WeilConjectures/Mathlib/Algebra/Homology/DerivedCategory/TStructure.lean:113,166,182,231`, assume properties of cohomology objects. Reading their signatures and proofs shows they do not assert the item about complex terms. They are not attachment candidates for this item.

## WANTED

None. All sources used are available in the read clone.

## Corrections and limitations

The item statement is unchanged. Its imported proof was empty; the split now supplies the argument rather than moving the conclusion to a new node. The existing Mathlib-search records have been retained and their results refreshed from actual command outputs. Searches in the DAG and whole imported blueprint for stupid truncations, bounded complexes and triangulated subcategories found no duplicate of this abstract termwise assertion. The existing `lem-weil-pbc-complex-ses-triangle` provides the general theorem needed, so a module-specific stupid-truncation sequence node is unnecessary. The fixed chapter and unit route is unchanged; no unit records require editing.

Nothing remains unfinished in this split. This is a natural-language stage-1 delivery; no Lean was written or compiled.

## Not duplicates

No new nodes. In particular, the module-specific `lem-sf-module-stupid-truncation-short-exact` is restricted to modules over a commutative ring and cannot directly justify the assertion for an arbitrary abelian category. Its degreewise exactness argument is elementary and is written explicitly in Step 2 instead of generalized into another node.

## Review by NE

I read Stacks derived.tex, Tag 0FCP (`lemma-K-bounded-derived`), especially the displayed stupid-truncation triangles and the finite induction in lines 9112–9128. The proof extracts the construction, not the K-group conclusion. I also read Tag 0152 (`lemma-derived-canonical-delta-functor`, lines 3965–4006) to check the existing short-exact-sequence triangle node against its source. In the main-20261015 blueprint I read both the statement and proof of `lemma-weil-pbc-perfect-projection-formula`: this split supplies the bounded-complex generation argument implicit in its first paragraph. No SGA route is used.

For Step 1 I opened `def-weil-abstract-derived-category` and checked the cochain convention, the localization and the zero-complex interpretation. The tails are defined explicitly, and their endpoint identifications use the assumed support bounds. Empty intervals are handled before induction. For Step 2 I opened both that node and `def-sp-abelian`: the category has zero objects and kernels/cokernels, and all three degreewise sequences displayed are identity/zero exact sequences. I checked the chain-map identities at the cutoff; the tail is the subcomplex in degrees at least n, with no smart-truncation kernels introduced.

For Step 3 I read the full statement of `lem-weil-pbc-complex-ses-triangle`. It asserts exactly the distinguished triangle for every degreewise short exact sequence in an abelian category whose derived category exists. These are precisely our hypotheses. No injective resolutions, projective objects, naturality theorem, bounded-derived comparison or additional smallness hypothesis is used here. The statement is quoted verbatim in citations.json.

For Step 4 the derived-category definition states that Q commutes with shifts and gives the sign convention. This places C^n[0][-n] in degree n, with zero differential, so the shifted single object agrees with E_n. Membership follows from the item's own hypotheses, not from a theorem about cohomology. For Step 5 I opened `def-weil-triangulated-category` and checked (TR2). Two rotations give the known objects E_n and T_(n+1)[1] as the first two vertices, and the resulting third vertex is T_n[1]; shifting back gives T_n. Thus even interpreting the closure assumption as only closure for the literal third vertex suffices. The induction claim, its finite range, zero base, successor case and endpoint are all explicit.

I checked the zero complex; a>b (no terms); a=b (one term, in any integer degree); gaps of zero terms; nonzero differentials in a two-term complex; and negative bounds. None requires retract closure, flatness, projectivity, bounded cohomology devissage or replacing terms by cohomology. I audited delivery-errors B–E against these actual sources and statements: there are no new-node form defects, no hidden non-elementary assertion beyond the cited triangle theorem, no relabelled copy of the item, and no unsupported hypothesis. Every proof step is shorter than 2000 characters. The final induction is a finite repetition of the already justified triangle step, rather than a new hidden lemma.

I inspected the search hits. Mathlib's `stupidTrunc` is a construction, `mem_of_hasInductedTStructure` additionally requires an induced t-structure and does not state termwise generation, and the generic triangulated-subcategory API supplies closure rather than the finite devissage theorem. The second semantic phrasing also returned t-structure and cohomological-boundedness declarations, not this item. The Mathlib verdict remains no match.
