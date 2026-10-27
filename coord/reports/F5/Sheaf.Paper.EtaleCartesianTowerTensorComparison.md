## What changed

Proved `AlgebraicGeometry.ProEtale.EtaleCartesianTower.beta_isIso` in
`Sheaf.Paper.EtaleCartesianTowerTensorComparison` using the existing finite-etale
normalization theorem. Smoothness of q follows from its specified relative dimension;
smoothness of qQ follows from the actual Cartesian square. Normalization supplies
invertibility of the specified target sigma and its inverse-free beta equation.
`CategoryTheory.IsIso.of_isIso_fac_right` cancels the invertible target-unit and
sigma composite, since the other side is a composite of canonical isomorphisms.
No definition, statement, public import, or target is changed.

Removed two unused private proof imports. The geometric argument uses Mathlib's
base-change stability directly, and the cancellation lemma is already available
through the retained imports.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.ProEtale.EtaleCartesianTower.beta_isIso`.

The original named theorem
`AlgebraicGeometry.ProEtale.EtaleCartesianTower.etale_cartesian_tower_tensor_comparison`
remains `sorry`, with its original source, complete six-step proof docstring, and
node `lem-pur-etale-cartesian-tower-tensor-comparison` unchanged. Its four tensor
comparison identities have not been claimed as proved. Added holes: zero.
Split-off statements: zero. This is a partial proof delivery, not a decomposition.
The beta proof applies uniformly to identity arrows and empty schemes: it uses only
base-change stability and categorical cancellation of isomorphisms.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres`
and `Mathlib.CategoryTheory.Adjunction.Mates`. The former's fibre-dimension theorem
is unnecessary for beta invertibility; the latter is unnecessary as a direct import
for categorical cancellation. No module is withdrawn. No DAG dependency is claimed
pruned: the unfinished main theorem retains its complete planned dependency list,
including dependencies it may need for its remaining tensor identities.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. Smoothness of q is supplied explicitly by
`SmoothOfRelativeDimension.smooth`; smoothness of qQ uses the supplied Cartesian
square, so the argument does not assert that the outer square is Cartesian.
The proof uses normalization's actual `target_sigma_iso` and
`smooth_base_change` fields, rather than assuming beta invertibility independently.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
