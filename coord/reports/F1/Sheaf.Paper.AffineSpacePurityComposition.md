## What changed

Filled the five coordinate and endpoint helper proofs in
`lean/Sheaf/Paper/AffineSpacePurityComposition.lean`, preserving every existing signature,
definition and docstring. Block projection compatibility follows by induction, using
naturality of the affine-line projection under equality transport. Two proved private
helpers give extensionality of maps into the iterated affine line and the inverse-permutation
calculation. The coordinate isomorphism lies over its base by the existing projection equation.
The positive exceptional endpoint is its defining formula; uniqueness of the positive
comparison is uniqueness of a morphism heterogeneously equal to the fixed comparison.

The displayed composition and coordinate-invariance theorem
remains the original named hole; the delivery does not claim to prove it.

## Proved and sorry left

Closed 5 of the original 6 holes, all in namespace
`AlgebraicGeometry.ProEtale.AffineSpacePurity`:

- `blockProjection`.
- `coordinateMap_isIso`.
- `coordinateProjection`.
- `exceptionalPositive_obj_eq`.
- `positiveComparison_existsUnique`.

Added 0 holes and split off 0 statements. The sole remaining hole is
`AlgebraicGeometry.ProEtale.AffineSpacePurity.affineSpacePurityComposition`, attached to
`prop-pur-affine-space-composition-law`. Its original full natural-language proof remains
in its docstring and node. This is a partial proof delivery, not a decomposition.

The coordinate proofs include dimension zero and arbitrary permutations, including identity,
and use no affineness or nonemptiness assumption on the base. The block induction includes
either block of length zero. Positive endpoint proofs apply to every successor dimension.

## No longer needed

Nothing. The composition and coordinate-invariance theorem `affineSpacePurityComposition`
is still `sorry`, so the private imports of the module (the modules of the node's planned proof
dependencies, among them the unit-route module `Sheaf.Paper.IntrinsicCoefficientTwistsUnrestricted`)
remain the plan for its proof and stay imported (stage 3 §2: imports are pruned once the proof
compiles). The delivered pruning of 22 private imports was reverted by the reviewer
(FIX, 2026-10-26); the five helper proofs compile with them. The existing DAG proof and proof
dependencies are retained, because the remaining theorem has not changed route.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The five helper holes are ordinary geometric or definitional
identifications and do not require the main purity-composition argument. The currently stated
regrouping and trace dependencies remain relevant to the unfinished main theorem.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
