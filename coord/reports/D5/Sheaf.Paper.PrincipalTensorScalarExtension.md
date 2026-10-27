## What changed

Proved `AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_tensor_scalar_extension`
without changing its statement. The proof compares derived tensor and restricted scalar
extension with the same termwise tensor on K-flat complexes, then descends their natural
isomorphism and its specified unit/transition equations through localization.

Added proved theorems `CategoryTheory.Mod.KFlatScalarTower.natural_computation` and
`CategoryTheory.Mod.KFlatScalarTower.derived_realization` to the
unclaimed `Sheaf.Algebra.Homology.InternalKFlatScalarTowerRealization` module. It exposes
the natural computation already used by the proof of its existing realization theorem.
Every existing signature and definition in that module is unchanged. The existing
realization proof now reuses natural_computation instead of repeating its calculations.
Its sole existing direct importer,
`Sheaf.SixFunctors.ProEtale.DerivedCompletion`, needs no adaptation. The addition is
recorded in `coord/changes/D5-principal-tensor-natural-computation.md` and attached to the
existing scalar-tower node.

The item adds a private proof import of the scalar-tower module. The scalar-tower module
adds private proof imports of the existing bifunctor single-complex naturality and
comparison modules. Generic private helpers prove the tensor comparison, its K-flat
invertibility and normalization, and localization descent. The generic derived realization
theorem combines them, and the assigned theorem specializes it to the native quotients.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.PrincipalNormalization.principal_tensor_scalar_extension`
(`lem-pe-principal-tensor-scalar-extension`).

Added 0 holes. No `sorry` remains in either delivered Lean module. The public supporting
theorems `CategoryTheory.Mod.KFlatScalarTower.natural_computation` and
`CategoryTheory.Mod.KFlatScalarTower.derived_realization` are proved. This is a
proof, not a decomposition.

Both delivered modules compiled together with lcompile.py --all. The scalar-tower
module took 56.2 seconds and the assigned module took 16.1 seconds. Formatting warnings
from that run were corrected before delivery. The localization argument is generic
over its abelian category to avoid expanding internal-module structures during matching;
large balanced-tensor comparisons are locally irreducible after their formulas are proved.

## No longer needed

None. Both existing public imports remain necessary for the statement. The four stated
proof dependencies remain needed: native scalar realization, derived completion, derived
monoidal structure, and the derived-category localization API. No node or module is
withdrawn. This proof follows the existing unit route.

## Where the brief, the DAG or earlier work was wrong

The stated objectwise scalar realization is not by itself enough to choose natural
components: arbitrary choices of its existential witnesses need not be natural. Its proof
already has a canonical natural computation map. Exposing that proved map supplies the
missing interface without another existence assumption or a split of this obligation.

Searches: LeanFinder found ordinary ModuleCat extension/restriction tensor formulas;
Loogle and grep supplied generic derived/localization APIs. The project source supplies
`mapBifunctorSingle₂Iso`, its naturality, and the K-flat computation counit. These
are used directly; no alternative constant-coefficient realization is introduced.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
