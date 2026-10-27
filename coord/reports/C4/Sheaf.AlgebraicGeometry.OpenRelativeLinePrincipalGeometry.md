## What changed

Proved `AlgebraicGeometry.openRelativeLine_principal_geometry` with its exact original
statement and public imports. No definitions or other modules were changed.

The proof uses the existing standard-smooth polynomial presentation, transported from
one multivariable coordinate to `Polynomial R`, to prove smoothness of the specified
`Spec (Polynomial.C)` projection directly. Mathlib supplies Noetherianity, permanence
of morphism properties, affineness of principal opens, and relative-dimension
composition. The finite subcover is enumerated by `Fintype.equivFin`; prime-ideal product
membership proves the intersection formula. A clopen inclusion is affine by
`isAffineHom_of_isInducing`, so there is no need to construct its closed immersion.

Added private proof imports `Mathlib.Algebra.MvPolynomial.Equiv` and
`WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth`. Updated the item's DAG proof,
proof dependencies and proof origin to describe this route, and removed its obsolete
`sbc-lem-affine-space-smooth` tool-use entry. No unit statement or unit step is bypassed:
the item is below the realized steps of `sk-thm-properbasechange`.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.openRelativeLine_principal_geometry`
(node `lem-weil-pbc-open-relative-line-principal-geometry`).

Proved 1 of 1 sorries; added 0 holes; split off 0 statements; 0 sorries remain.
The single-file compile passed without warnings. The explicit `#print axioms` check
reported only `propext`, `Classical.choice` and `Quot.sound`.

## No longer needed

Removed these private proof imports:

- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
- `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`.

Removed the following dependencies from this item's proof route (their declarations
are preserved throughout the library):

- `def-nagata-relative-affine-space`.
- `sbc-lem-affine-space-smooth`.
- `lem-weil-pbc-lfp-affine-opens-finite-presentation`.
- `lem-weil-pbc-lft-affine-pairs`.
- `def-weil-finite-type-morphism`.
- `lem-weil-pbc-qcqs-morphism-permanence`.
- `lem-weil-pbc-etale-composition-cancellation`.
- `lem-weil-pbc-etale-smooth-zero-dimensional-fibres`.
- `def-weil-closed-immersion`.
- `lem-weil-pbc-closed-immersion-finite`.

The general affine-space construction and smoothness theorem are unnecessary because
the polynomial chart is handled directly. Mathlib's smooth/finite-presentation instances
supply local finite type without the separate affine-pair presentation route.
Noetherian source topology supplies quasi-compactness without the general qcqs lemma.
Mathlib already gives relative dimension zero for open immersions and étale morphisms,
so no fibre-dimension computation or étale cancellation lemma is needed. The inducing
map with closed range makes the clopen inclusion affine directly, eliminating the
closed-immersion and closed-immersion-finite detour. The notion of finite type and the
affine-space definition still belong to the statement's background; only their separate
proof dependencies have been removed.

Only the removed Sheaf import is an open proof module newly avoided by this item;
no module is withdrawn, and no claim is made that other parents cease to need it.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original eight-step plan is valid but asks for
unnecessary work: an identification with the relative affine-space construction,
an explicit zero-dimensional-fibre argument, a closed-immersion construction for the
clopen inclusion, and affine-pair presentation arguments. The complete proof uses
already proved Mathlib/source APIs for these tasks. Empty opens and empty finite
étale/clopen pieces require no exceptional hypothesis. The intersection identity even
holds for the empty indexing finset, though the theorem only requests nonempty ones.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
