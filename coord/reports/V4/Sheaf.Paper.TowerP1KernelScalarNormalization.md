## What changed

Proved the complete assembly of `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1KernelScalarNormalization`
from two strictly smaller geometric statements. Its signature is unchanged.

The proof supplies the canonical sum-comparison isomorphism from preservation of
biproducts. It derives inverse and trace base change by cancellation in the forward
splitting square, and exchange invertibility from the same square. It proves unique
degree-zero lifts using Mathlib fullness and faithfulness, proves equality detection
for abelian tower maps directly on sections, and uses the exact evaluation/single
natural isomorphism to detect equality only between degree-zero derived objects.
Finally it cancels the invertible endpoint of each finite commuting square to obtain
the evaluated identity and then the tower scalar identity for both projections.

Relocated the eleven original data declarations, without changing signatures or
bodies, to `Sheaf.Paper.TowerP1KernelScalarData`, publicly re-exported from the original
module. This allows the two independent geometric proof dependencies to use the
same definitions without an import cycle. This is a dependency factorization, not
a response to slow compilation. The change record is
`coord/changes/V4-kernel-scalar-data-location.md`.

The new lemmas are `Sheaf.Paper.TowerP1KernelSplittingBaseChange` (normalized splitting
construction, forward square, canonical alpha isomorphisms) and
`Sheaf.Paper.TowerP1KernelFiniteComparison` (Cartier diagonal and finite commuting
squares with finite identities). Each has a named theorem, source, complete proof
in words, and its own DAG node. The original theorem contains no `sorry`.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.SpTowerP1.towerP1KernelScalarNormalization`.
Added two holes, so this delivery is a decomposition, not a net hole reduction:

- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1KernelSplittingBaseChange`,
  node `lem-sp-tower-p1-kernel-splitting-base-change`.
- `AlgebraicGeometry.ProEtale.SpTowerP1.towerP1KernelFiniteComparison`,
  node `lem-sp-tower-p1-kernel-finite-comparison`.

All six private categorical helpers are proved. No hole is inside a definition,
private helper, or the main proof. The data module contains zero holes.

## No longer needed

No mathematical module or unit is withdrawn. The geometric dependencies remain
needed through the two split lemmas. Their imports are now in those modules:
`Sheaf.Paper.TowerP1EtaleOriginComparisons`, `Sheaf.Paper.TowerChernPullback` and
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`.

The original public imports are preserved transitively by the new public data module:
`TowerP1ProjectiveCoordinates`, `FiniteP1ArbitraryBaseIntegrals`, derived full
faithfulness and pretriangulated categories, `PicardFunctor`,
`SmoothPurityTowerClasses`, `FixedEtaleOriginWitness`, `ProjectiveSpace`,
`CoefficientExtensionFinite`, `SmoothPurityCoefficientTowers`,
`SmoothPurityCoefficientTowersAbelian`, and `SemilinearDerivedSections`.
These remain dependencies of the unchanged public interfaces.

The main node no longer directly cites `det-sp-tower-classes`,
`lem-sp-tower-p1-etale-origin-comparisons`, `def-pc-projective-space-twist`,
`lem-sp-tower-chern-pullback`, `lem-coef-semilinear-derived-sections`,
`lem-sp-tower-p1-arbitrary-base-integrals`, or `def-weil-l-adic-coefficient-extension`:
they are used by the geometric sublemmas or data interfaces. Removed the main node's
obsolete direct tool-use entries for projective-space-twist and semilinear-derived-sections;
the degree-zero Mathlib tool-use remains. No library module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The DAG route is retained. The existing declarations do not directly state the
normalized splitting square or the finite trace comparison for an arbitrary
`KernelSplittingData`. Those are the two genuine geometric steps now isolated.
All later categorical consequences are proved, including the restriction of equality
detection to degree-zero coefficient objects; no faithfulness of general derived
evaluation is asserted.

Read the latest blueprint proof and the unit record. Checked empty-base and both
projection cases, positive level n+1 (including n=0), arbitrary ramification, and
the positive divisor sign. The new statements impose no Noetherian, finite-type,
flatness, or finite-Tor assumption. Neither new statement has the original full
conclusion: one is geometric base change without scalar identities, the other is
finite comparison without tower base change or tower scalar identities.

Mathlib searches used LeanFinder, LeanSearch, Loogle, and grep; the result log is
recorded on the new nodes. Matrix/algebraic trace and tensor-base-change search
results do not match these sheaf-tower statements. Mathlib singleFunctor full
faithfulness does close the final algebraic part and is used directly.

## New nodes

`def-sp-tower-p1-kernel-scalar-data` owns only the eleven original public data
interfaces relocated verbatim to `TowerP1KernelScalarData`. The parent theorem keeps
its original name and statement, and adds this owner to its statement dependencies.
This owner eliminates import cycles.

`lem-sp-tower-p1-kernel-splitting-base-change` states steps 1–2 of the original plan,
plus the canonical composition-source isomorphisms. It does not assert finite
normalization or either diagonal scalar identity.

`lem-sp-tower-p1-kernel-finite-comparison` states steps 4–5 of the original plan for
a given normalized splitting. It does not assert a tower scalar identity or any
splitting base-change square. The proof combining these statements with the
categorical steps 3, 6 and 7 is complete in the item module.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
