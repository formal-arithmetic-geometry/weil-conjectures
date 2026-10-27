## What changed

Replaced the body of `AlgebraicGeometry.ProEtale.tower_firstChern_pullback` by a composition
argument in the ordinary derived category of entire coefficient systems. Its statement is
unchanged. The proof factors the specified Chern morphism as the inverse coefficient-unit
comparison, realization of the integral line-bundle class, and the root-target comparison.
It applies naturality of the realization comparison, substitutes integral-class pullback,
and cancels the two coefficient-unit isomorphisms. The canonical shift comparison stays
explicit. No equality of general derived maps is inferred from their finite evaluations.

Added `Sheaf.Paper.TowerIntegralClassPullback`, which constructs componentwise abelian-tower
inverse image, its exactness instances, the projection-induced full-units map, and the
integer/units comparison maps on towers and their derived categories. Its remaining theorem
is the integral line-bundle-class equation, with no torsion or coefficient extension.

Added `Sheaf.Paper.TowerChernRealizationPullback`, which defines the actual successive
coefficient-realization functor and its source and target comparisons, and proves
`firstChern_eq_realization` by functoriality. Its remaining theorem is a natural comparison
on all integral derived objects with the two endpoint equations. It has no line bundle or
Chern-class argument. Both remaining statements carry the corresponding parts of the
original seven-step proof, including the positive-kernel sign calculation, in docstrings
and new DAG nodes. They are separate parts of the original argument rather than aliases
for the original assertion.

The main module now privately imports the realization module. Existing public imports,
public signatures, options and docstrings are preserved. No existing definition or
statement is changed, and no source-library file is edited.

## Proved and sorry left

This is a decomposition: one original hole is closed and two lower holes are added.

Closed:

- `AlgebraicGeometry.ProEtale.tower_firstChern_pullback`
  (`lem-sp-tower-chern-pullback`), using the two intermediate statements.

New proved support:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.abPull_additive`
- `AlgebraicGeometry.ProEtale.SpTowerClasses.abPull_limits`
- `AlgebraicGeometry.ProEtale.SpTowerClasses.abPull_colimits`
- `AlgebraicGeometry.ProEtale.SpTowerClasses.firstChern_eq_realization`
- The naturality and group laws in the explicit `unitsDirect`, and tower naturality in
  `integerPull` and `unitsPull`, are proved in their constructions.

Every remaining sorry in the delivery:

- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_integralClass_pullback`
  (`lem-sp-tower-integral-class-pullback`). This is steps 1--3: identify the specified
  Picard class with the glued full-units extension and transport that extension under f.
- `AlgebraicGeometry.ProEtale.SpTowerClasses.tower_chernRealization_pullback`
  (`lem-sp-tower-chern-realization-pullback`). This is steps 4--7: transport universal
  scalar comparisons to the recorded models and check the two normalized endpoints.

No sorry remains in the item module. No definition contains sorry. No axiom is added.
The source and target normalization assumptions remain required by the realization lemma.
The integral lemma works for arbitrary f without ell-invertibility hypotheses.

Validation: both new modules compile through `lcompile.py --all`, and the final item
module compiles through `lcompile.py` with exit code 0. The parent proof contains no
unfinished tactic goals; its final step uses only categorical associativity.

## No longer needed

Removed the following direct private proof imports from the item module, replacing them
with `Sheaf.Paper.TowerChernRealizationPullback`:

- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`
- `WeilConjectures.CategoryTheory.Sites.Torsor`
- `Sheaf.CategoryTheory.ExtOneExtensionClassification`
- `Mathlib.Algebra.Homology.DerivedCategory.Ext.Map`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.CategoryTheory.AlgebraDiagramPullbackExtensionCoherence`
- `Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`
- `Mathlib.Algebra.Homology.DerivedCategory.TStructure`
- `Sheaf.CategoryTheory.TorsionSheafConstantModule`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`
- `Sheaf.Paper.TateTwistLocallyFree`

Their mathematical work is retained where needed in the two intermediate nodes' proof
plans; this delivery claims no dependency module or mathematical node as globally pruned.
The parent node's old direct proof-dependency and tool-use lists are replaced by its two
actual intermediate dependencies. The unit route is retained, with no unit withdrawal.

## Where the brief, the DAG or earlier work was wrong

The original seven-step mathematical plan needs additional Lean glue between the generic
interfaces and the specialized tower objects. In particular, generic scalar coherence
alone is not a direct lemma about the recorded `Chern` reductions, their scalar models,
and their section-normalized `CoefficientPullback` and `LinePullback` endpoints. The new
realization statement isolates precisely that glue and the two-term Kummer calculation.
Likewise the torsor classification interfaces do not directly state the naturality of
`lineBundleClass`, which includes site change, full units, constant towers and exact-derived
single comparisons. The integral statement isolates that identification without assuming
that inverse image of all units is an isomorphism.

Searches of Mathlib by LeanSearch, LeanFinder/Loogle and source grep found no direct tower
Chern, integral-class or coefficient-realization theorem. Existing curve Picard pullback
results impose curve hypotheses absent here. Blueprint searches for line-bundle pullback,
integral line-bundle and coefficient realization found no matching blueprint statement.
The generic algebra-diagram comparison remains the tool for the second intermediate;
its actual signature was read, including universal counits and unit normalization.

Both statements were checked on trivial bundles, identity morphisms, empty schemes,
nonflat scheme maps, first positive level, and ramified E. The units map is merely a
morphism. Exactness is topos inverse-image exactness, not scheme-theoretic flatness.
The sign calculation is the original h^0=id_M calculation, not a changed convention.

## New nodes

`lem-sp-tower-integral-class-pullback` is attached to
`Sheaf.Paper.TowerIntegralClassPullback.tower_integralClass_pullback` in namespace
`AlgebraicGeometry.ProEtale.SpTowerClasses`. It retains the integral extension argument
from original steps 1--3. Its support constructions are explicit and contain no holes.

`lem-sp-tower-chern-realization-pullback` is attached to
`Sheaf.Paper.TowerChernRealizationPullback.tower_chernRealization_pullback` in the same
namespace. It retains the scalar and Kummer-target argument from steps 4--7 and states
naturality before applying it to a line-bundle class. Its factorization lemma is proved.

No change record is needed for an existing interface: all existing statements and
definitions are unchanged. The new public support belongs to the two new nodes.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
