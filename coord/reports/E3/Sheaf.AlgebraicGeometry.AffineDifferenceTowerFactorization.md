## What changed

Filled the proofs of `AlgebraicGeometry.AffineDifferenceTower.factorization` and
`AlgebraicGeometry.AffineDifferenceTower.exists_compatible_charts`, preserving their
statements and all existing definitions. Added only proved private coordinate and
pullback helpers in the item module. No consumer adaptations are needed.

The factorization proof constructs the universal property of the ordered affine
product using `Fin.addCases` and `AffineSpace.hom_ext`. It identifies the untranslated
charts by cancelling affine-space base-change squares, then composes with explicit
translation isomorphisms. Pullback cancellation gives the two restriction squares.
Etaleness, separatedness, local finite type, affineness and quasi-compactness follow
from the corresponding Mathlib permanence lemmas and instances. The diagonal and
coordinate identities are equalities of scheme maps, checked on coordinate sections.

The local-existence proof uses the source-library normal form with the prescribed
relative dimension for g. A standard smooth presentation of f is refined inside its
chosen affine g-chart by `exists_basicOpen_le_appLE_of_appLE_of_isAffine`, then the
source-library normal-form construction gives the f-chart. Thus no separate
uniqueness-of-dimension argument is needed. Restrictions retain the specified
relative dimensions and all morphism properties.

Updated the item's DAG proof and dependencies to record these actual arguments.
The source is the current blueprint composition-coherence proof, Step 1, with
Stacks morphisms.tex, normal form Tag 054L and etale base change/composition
Tags 02GO/02GN. Empty coordinate blocks use the same `Fin.addCases` universal
property; the construction has no nonemptiness assumptions.

## Proved and sorry left

Holes closed: `AlgebraicGeometry.AffineDifferenceTower.factorization` and
`AlgebraicGeometry.AffineDifferenceTower.exists_compatible_charts`
(node `lem-pur-affine-difference-tower-factorization`).

Holes added: none. Sorries left in the delivered module: none. Two of two existing
holes are filled, with zero split-off statements. Validation: remote single-file
compilation and the delivery tool's complete preflight (results recorded at delivery).

## No longer needed

The proof-only import `Sheaf.AlgebraicGeometry.EtaleLocalNormalForm` is unnecessary:
the adopted source library already proves the prescribed-dimension normal form and
the standard-smooth affine-chart construction needed here. The proof-only import
`Mathlib.CategoryTheory.Limits.MorphismProperty` is also unnecessary: no
finite-limit preservation assertion is used.

The following former DAG proof dependencies are unused by the completed route:
`lem-weil-pbc-quasicompact-affine-surjection`,
`lem-weil-pbc-quasi-separated-affine-cover-criterion`,
`def-weil-pbc-scheme-conventions`, `lem-weil-pbc-lft-pointwise-criterion`, and
`lem-weil-pbc-lft-affine-pairs`. Direct Mathlib instances give quasi-compactness
for maps between affines and local finite type of restrictions; no separate
pointwise finite-generation or quasi-separated affine-cover argument is needed.
No module is withdrawn: the item and its parent/unit dependencies are preserved.
No declaration or public import in `lean/WeilConjectures/` is changed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or disputed. The planned local-existence
argument was longer than necessary because the source library already has the
normal form with its dimension fixed. The parent module's unfinished geometry
and chart-geometry theorems are not used: their DAG depends on this item, so using
them would reverse the intended dependency. The required geometric squares are
proved directly here instead.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
