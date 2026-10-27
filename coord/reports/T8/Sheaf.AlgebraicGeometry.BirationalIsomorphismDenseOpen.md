## What changed

Filled `AlgebraicGeometry.exists_dense_open_isIso_of_separated_birational` in
`Sheaf.AlgebraicGeometry.BirationalIsomorphismDenseOpen`. Added a private proof import of
`Sheaf.AlgebraicGeometry.BirationalCommonDenseOpens` and followed the existing three-step plan.
The common-open inclusion is closed by `IsClosedImmersion.of_comp`, because its composite with
the separated target restriction is an isomorphism. Its range is dense by `Dense.preimage`,
so the source open equals the full inverse image. Updated the node's proof description to
match these Lean steps. The declaration signature and public imports are unchanged.

Validation: `lcompile.py` accepted the final module without errors or warnings (4.1 seconds).

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.exists_dense_open_isIso_of_separated_birational`
(node `lem-sfb-birational-isomorphism-dense-open`). No holes remain in the item, and none
were added or split off. The proof uses the existing, still unproved declaration
`AlgebraicGeometry.exists_common_dense_opens_isIso_of_birational`
(node `lem-sfb-birational-common-dense-opens`), as intended by the stage-3 dependency plan.

## No longer needed

Removed redundant private imports `Mathlib.AlgebraicGeometry.OpenImmersion` and
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; their declarations are available
through the remaining imports. No dependency nodes or modules are pruned: every declared
proof dependency is used.
The closed-section argument is implemented through its general Mathlib `of_comp` lemma,
without explicitly constructing the section and inverse isomorphism.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The finite-component and generic-stalk hypotheses are passed
unchanged to the common dense opens theorem. The remaining argument uses neither reducedness
nor nonemptiness. No new declarations, nodes, or interface changes were needed.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
