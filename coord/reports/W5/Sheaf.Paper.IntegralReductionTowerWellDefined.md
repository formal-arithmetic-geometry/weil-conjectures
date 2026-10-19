## What changed

Prove the two remaining theorems in
`Sheaf.Paper.IntegralReductionTowerWellDefined` by reusing the existing unrestricted
interface for exactly the same completed coefficient sheaf and projection.

`integralTowerMaps_existUnique` uses the unrestricted unit and transition as witnesses.
Uniqueness of transitions is proved by transporting the source to its specified
sheafification, forgetting to abelian sheaves, applying the sheafification universal
property, and inducting on presheaf tensors. The legacy selected pair consequently
equals the unrestricted pair.

The two complex abbreviations and the resolution-isomorphism definition now directly
reuse the canonical unrestricted constructions. Naturality of the quotient comparison
on the augmentation identifies the former and current resolution formulas, as detailed
in `coord/changes/W5-tower-complex-abbreviations.md`. The finite comparisons and their
restrictions therefore agree. Substitution into the proved unrestricted tower theorem
proves `integralReductionTowerWellDefined` without changing its statement.

Replace the obsolete import of the legacy tower in
`Sheaf.Paper.IntegralReductionTowerUnrestricted` with its actual prerequisites,
`CompletedIntegralCoefficients` and `Functor.OfSequence`, to remove the import cycle.
The module is unclaimed, and no declaration is changed. See
`coord/changes/W5-unrestricted-tower-import.md`. Recompilation exposed an expensive
transition-naturality conversion in the unclaimed
`Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`. Its proof now gives the
published transition the private helper's functor type and applies naturality after
whiskering with localization, rather than expanding scalar-extension existence
witnesses. The two complex functors agree definitionally. A local irreducibility
attribute also protects the completed coefficient construction. All its signatures
and public definition bodies stay unchanged. The shared node's proof records this
specialization as well as the unchanged common-roof argument.

## Proved and sorry left

Closed 2 existing holes:

- `WeilConjectures.integralTowerMaps_existUnique`.
- `WeilConjectures.integralReductionTowerWellDefined`.

Both realize `lem-weil-integral-reduction-tower-well-defined`.
No holes remain in the item; no holes are added or split off.

The adapted dependency retains its one existing hole unchanged:
`WeilConjectures.unrestrictedIntegralTransition_existsUnique`
(`def-weil-integral-reduction-tower`). Its statement and proof are unchanged.

## No longer needed

Removed the item's direct proof imports of
`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
`Sheaf.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass`,
`WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated`, and
`Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`.
The proof publicly imports the existing unrestricted interface because its complex
abbreviations now reuse the canonical definitions; its proof continues
to use the common-roof dependencies, so these are direct-import removals only.

The obsolete public import `Sheaf.Paper.IntegralReductionTower` is removed from
`Sheaf.Paper.IntegralReductionTowerUnrestricted`. No definition or theorem from that
legacy module is used by the unrestricted tower. This removes an incidental reverse
import edge, allowing the legacy theorem to reuse its existing unrestricted proof.

No mathematical proof-dependency node is globally pruned: the common-roof, K-flat
resolution, tensor and derived-change-of-rings results are still used by the existing
unrestricted theorem. No blueprint unit or step is bypassed; the unit has no realized
statement or steps at this node.

## Where the brief, the DAG or earlier work was wrong

The brief names the legacy finite-field module, while the node's current primary Lean
attachment is its already proved unrestricted counterpart. Their coefficient
constructions and canonical scalar-extension witnesses agree definitionally. The
apparent duplication of the tower proof was unnecessary. The unrestricted tower's
historical import of the legacy tower prevented direct reuse until this import repair.

The final three-file packet compiles cleanly with `lcompile.py --all`, in import
order: `IntegralReductionTowerUnrestricted` (7.6 seconds),
`IntegralReductionTowerWellDefinedUnrestricted` (32.4 seconds), and the assigned
module (47.2 seconds). All use the original compiler limits; there are no warnings. The unchanged consumers `IntegralOperationsWellDefined`,
`SfRationalLocalGlobalPowerTorsion`, and `IntegralReductionTower` also compile
against the repaired interface (16.0, 8.3, and 6.8 seconds respectively).
All 46 existing public declaration signatures across the three edited modules
(including all sixteen in the item) were checked textually against the shared source
and are identical.

The two complex abbreviations and the resolution computation now reuse their canonical
counterparts; see `coord/changes/W5-tower-complex-abbreviations.md`. No target or
existing theorem signature, universe, hypothesis, or conclusion changes. The proof
identifies the existing, uniquely normalized maps. The resolution computation refactoring
is justified by the quotient-comparison naturality identity recorded above.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
