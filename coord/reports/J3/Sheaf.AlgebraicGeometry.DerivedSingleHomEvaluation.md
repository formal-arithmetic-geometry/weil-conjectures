## What changed

Proved `AlgebraicGeometry.derived_single_hom_evaluation` in
`Sheaf.AlgebraicGeometry.DerivedSingleHomEvaluation`, preserving its statement,
universes, visibility, and all imports. A fully proved private categorical helper,
`localized_hom_evaluation`, packages the localization and naturality calculation
without unfolding the sheaf Hom construction.

The proof uses `derivedInternalHom_comparison` with the existing functorial
K-injective resolution. After fixing the source at the unit, it composes the
comparison with the given natural isomorphism `e` and the inverse of the localized
resolution map. Mathlib's fully faithful localization precomposition descends
this to `j`. For each K-injective `I`, `quasiIso_homComplex_map` applied to the
resolution map and the identity on `B[0]` supplies the isomorphism `c`.
Naturality of the comparison, of the Hom bifunctor, and of `e`, followed by the
two inverse cancellations, proves the required equality.

The existing node's three-step route is implemented unchanged, so no node edit
is needed. The private helper is proved categorical glue from Mathlib's
localization precomposition API, not a new mathematical dependency or a split.
The theorem locally respects reducibility during elaboration and has a documented
heartbeat allowance for the nested scheme/module comparisons.

Searches ran through `msearch.py`: LeanFinder on derived unit Hom evaluation
returned single-functor and ordinary derived-functor APIs, not this compatibility
statement; Loogle found the Mathlib localization precomposition API; grep found
its bifunctor/currying infrastructure. Local searches also found the already
proved `derivedInternalHom_unit_iso`, whose construction informed this proof
but whose conclusion alone does not supply the required compatibility.
Read the two dependency nodes and their Lean signatures, the unit record,
and Stacks Tags 08J7 and 0A95 at their official web pages (the literature tree
is not populated on this machine).

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.derived_single_hom_evaluation`
(node `lem-sc-derived-single-hom-evaluation`).

No holes added or split off. No `sorry` remains in the delivered module;
`localized_hom_evaluation` is fully proved. The proof uses the existing
`CategoryTheory.derivedInternalHom_comparison` and
`CategoryTheory.quasiIso_homComplex_map` declarations, without changing them.

## No longer needed

None. All existing imports are retained. Both planned dependency nodes,
`def-pur-derived-internal-hom` and `lem-pur-rhom-well-defined`, are used.
No new module, node, or downstream adaptation is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The arbitrary comparison supplied by
`derivedInternalHom_comparison` suffices: the same comparison is used in both
`j` and `c`, so its components cancel by naturality. This does not require a
canonical choice or additional normalization theorem.

The zero morphism, zero sheaf, zero ring, and empty scheme need no separate
hypotheses: the calculation uses only naturality, functoriality, and inverse
identities. No boundedness or finiteness is introduced.

## Second reading by J3

1. Compared the delivered module with the repository version. The theorem signature, universes, visibility, and existing declarations are unchanged; only the proof and a private helper were added.

2. Compiled `lean/Sheaf/AlgebraicGeometry/DerivedSingleHomEvaluation.lean` successfully. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations in the delivered source. The theorem's remaining `sorryAx` dependency comes only from imported open statements.

3. Checked the helper calculation and the target proof against the existing localization and comparison APIs. The private helper is a strictly internal reduction, introduces no split-off statement, and the target statement is unchanged and mathematically preserved.

4. Reviewed the proof route and imports. The route follows the node's three steps through `derivedInternalHom_comparison`, localization fully faithful precomposition, and `quasiIso_homComplex_map`; all three imports are used and none can be removed. No shorter existing declaration was found.

5. Checked the DAG node and unit route. The node's statement, proof dependencies, and proof origin agree with the Lean proof, and the unit route remains realized unchanged.

Changed only the report by adding this second-reading record; no Lean or DAG repair was needed.
