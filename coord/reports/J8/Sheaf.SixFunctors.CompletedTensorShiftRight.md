## What changed

Proved the derived right shift theorem from the strict finite tensor tower comparison.
The proof constructs the product map, its square with 1-s, the cone isomorphism with
coefficients 1 and (-1)^r, and the Roos comparison. It proves naturality of these maps.
It proves stability of flat-term K-flat models under shifts. The
comparison-compatible descent uses the universal uniqueness property of the specified
completed tensor descent, postcomposes with the inverse shift, and cancels the defining
model comparisons. No separate construction of fully faithful good-model restriction
is required.

Added and proved `Sheaf.SixFunctors.CompletedTensorFiniteShift`, isolating the finite tower step.
Its theorem states the finite generator equation inline. The existing predicate
`WeilConjectures.integralCompletedTensorFiniteShiftFormula` stays in the item module and
in the item node (reviewer correction, 2026-10-21: the delivery had moved it to the new
module, which made the item statement use a declaration of a node outside its stmt_deps).
The item proof unfolds the predicate and applies the new theorem; the item imports the new
module with a plain `import`.

The small `completedTensorShiftSecond` wrapper becomes an abbreviation of the
same product functor, allowing kernel conversion to unfold it before the large
completed tensor descent. Its existing consumer keeps the identical definition.

The unclaimed coefficient module `Sheaf.Paper.CompletedIntegralCoefficients` changes
its commutative presheaf wrapper from `def` to `abbrev`, with signature and
body unchanged. This lets Lean unfold this wrapper before the underlying inverse
limit when comparing the two coefficient presentations. No coefficient data or
mathematical definition changes; no forced consumer adaptation is needed.

The unclaimed `Sheaf.Paper.IntegralDerivedOperations` packages its existing chosen
functor, model comparison and uniqueness proof in `IntegralCompletedTensorDescent`.
The original definitions now project the identical expressions from this record,
so their signatures and definitional values are preserved. Its universal field lets
the proof use the descent interface without re-expanding the full existence statement.

## Proved and sorry left

Closed the original hole in `WeilConjectures.integralCompletedTensorShiftRight`.
Also proved the new finite tower theorem
`WeilConjectures.integralCompletedTensorFiniteShift`
(`lem-sf-completed-tensor-finite-shift`) in this session: the right total-tensor
comparison, its formula on generators, conjugation and uniqueness of transitions,
and the two naturality conditions all have complete Lean proofs.

The requested module has zero of its original one holes left. The packet adds zero
holes; every private helper and the new finite theorem are proved. This closes one
original hole with no retained split. Existing holed dependencies are used through
their stated interfaces, including well-definedness and the uniquely characterized
ordinary reduction and tensor transitions.

## No longer needed

Removed the direct proof imports of
`Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`,
`Sheaf.Algebra.Homology.KFlat`, `Sheaf.Paper.IntegralOperationsWellDefined`,
`Mathlib.Algebra.Homology.DerivedCategory.Basic`,
`Sheaf.Paper.IntegralDerivedOperationsOnSlices`, and
`Sheaf.Algebra.Homology.KFlatIndependentCoefficients`,
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
The relevant definitions remain available through the required public imports;
the slice operations are not used. No source declaration or node is withdrawn,
and no whole module is claimed pruned from the targets' closure.

Removed the obsolete top-level `lem-pc-kflat-resolution` tool approval.
The derived proof does not invoke `lem-pc-kflat-resolution` or
`lem-weil-pbc-resolving-representative-whiskering`: the specified descent already
supplies the compatibility and uniqueness needed here. Those nodes remain needed by
other constructions, including the proof of well-definedness.

The original elementary tensor-sign and transition steps are proved in the new finite
node, rather than being repeated inside the derived proof. The unit's completed tensor
shift node remains realized by the original theorem.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The local coefficient-category interfaces
require care: the completed ring and its commutative presentation are definitionally
equal, but unrestricted unfolding expands the chosen limit. Local irreducibility
attributes keep comparisons at their named interfaces; coefficient data are unchanged.

## New nodes

`lem-sf-completed-tensor-finite-shift` isolates the original proof's finite signed tensor
comparison and strict quotient-transition compatibility. It is genuinely below the
requested theorem: the product, signed cone, Roos naturality, good-model stability and
localization arguments are implemented separately in the requested module.

Change records: `coord/changes/completed-tensor-finite-shift-interface.md` (the relocation was withdrawn by the reviewer) and
`coord/changes/completed-coefficient-presentation-reducibility.md`, and
`coord/changes/completed-tensor-descent-record.md`, and
`coord/changes/completed-tensor-shift-wrapper-reducibility.md`.

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
