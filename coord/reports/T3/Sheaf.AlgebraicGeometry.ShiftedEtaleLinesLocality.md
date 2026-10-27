## What changed

Filled both theorem bodies in `lean/Sheaf/AlgebraicGeometry/ShiftedEtaleLinesLocality.lean`.
The signatures, universes, hypotheses and conclusions are unchanged.

For `exists_shiftedEtaleLine_inverse`, construct the actual internal dual sheaf D of the
line sheaf F. Reuse the existing upstream evaluation isomorphism F tensor D ≅ unit.
On the nonempty members of a trivializing cover, identify F with the unit using a geometric
stalk. Cancel this local F in the evaluation pairing, with explicit unitors and inverse-image
monoidal comparisons, to trivialize D. Descent gives local constancy of D, and lifting each
separably closed geometric point to the cover identifies its stalk with A. The existing
flat single-object tensor comparisons, braiding and derived shift comparisons construct both
tensor inverse isomorphisms for single(D)[-n]. No witness is chosen from an unproved existence
theorem: D is the existing internal Hom, and all local witnesses are isomorphisms.

For `shiftedEtaleLines_descent`, choose a covering member over each point of X. This makes a
jointly surjective family indexed in the scheme universe even when the original index universe
is larger. Reuse upstream shifted-line descent. Applying degree -n cohomology to the resulting
single-object presentation identifies its sheaf with H^(-n)(M); transport all three required
properties along this isomorphism. The same subfamily and upstream derived conservativity
prove the morphism assertion. No finite subcover, boundedness, nonzero ring or nonempty scheme
hypothesis is introduced.

Updated the node proof and dependency list to describe this route. The change record is
`coord/changes/shifted-etale-lines-proof-context.md`, covering the public import removal and
file-local name-resolution and braiding-instance priority changes. All edits are in the assigned
sandbox; no source-library module is changed.

## Proved and sorry left

Closed 2 original holes:

- `AlgebraicGeometry.Etale.exists_shiftedEtaleLine_inverse`.
- `AlgebraicGeometry.Etale.shiftedEtaleLines_descent`.

Holes added: 0. Sorries left in the item or added by this delivery: none.
This is a proof from existing library interfaces, not a decomposition into new holed lemmas.
Compilation and delivery validation are pending.

## No longer needed

Removed these imports from the item:

- `Sheaf.AlgebraicGeometry.PointedEtaleStalk` (formerly public): the signatures use the existing
  ModuleCat-valued `pointSmallEtale.sheafFiber`, already exposed by the retained imports.
- `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: the geometric-point constructor is already
  exposed through the ordinary-etale library.
- `Sheaf.SixFunctors.EtaleStalkConstantComplexExactness`.
- `Sheaf.SixFunctors.EtaleDerivedPullbackStalk`.
- `WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtension`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction`.
- `Sheaf.CategoryTheory.RingedSiteModules`.

The corresponding obsolete top-level tool approvals are also removed, in their original order.

The exact ordinary-etale comparisons and flat single-object tensor calculations are already
proved by the upstream modules exposed through the retained AffineSpace import. The dual is
trivialized by cancellation in the evaluation pairing, so no generic ringed-site bridge or
internal-Hom restriction lemma is needed. Stalks are handled at separably closed points directly,
so no field-extension comparison is needed. These removals do not withdraw or delete any module
from the shared library; independently needed upstream dependencies remain intact.

The following old proof-dependency edges are removed from this node:

- `def-weil-geometric-point`.
- `lem-sfb-etale-stalk-constant-complex-exactness`.
- `lem-sf-etale-derived-pullback-stalk`.
- `lem-weil-pbc-geometric-point-field-extension`.
- `lem-pur-sheaf-line-evaluation-inverse-pair`.
- `lem-pc-bounded-above-flat-kflat-site`.
- `lem-pc-sheaf-modules-tensor-closed`.
- `prop-weil-pbc-inverse-image-modules-exact`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-sfb-localized-site-tensor-restriction`.
- `def-weil-sheaf-of-modules-category`.

There are no current Lean importers of the item (`tools/downstream.py` reports 0), and import
pruning will be checked by the delivery tool. The item remains needed by its DAG parents and is retained.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically valid but unnecessarily used general ringed-site and
unbounded complex interfaces where the adopted ordinary-etale library already has the needed
evaluation, flat single-object tensor and descent theorems. The upstream descent interface has
an index-universe restriction; selecting the subfamily indexed by points removes that restriction
without changing the theorem statement. The specified cohomology witness requires an additional
explicit transport, which is included here. No statement correction or unit-route change.

The compiler initially returned "no answer from the compile server" for multiple requests.
A subsequent service reply reports a missing published Mathlib.olean artifact before reading
the item. Neither reply gives Lean diagnostics about these proofs. Validation is retried
through the required tools; no launcher or service files are changed.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
