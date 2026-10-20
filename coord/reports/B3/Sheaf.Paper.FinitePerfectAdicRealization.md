## What changed

Restored `lean/Sheaf/Paper/FinitePerfectAdicRealization.lean` byte-for-byte from
`quarantine/Sheaf/Paper/FinitePerfectAdicRealization.lean`. Its theorem remains the
single assigned `sorry`, with its original signature and proof plan unchanged.

Change record: `coord/changes/B3-restore-full-finite-perfect-model-interface.md`.

The assigned file could not compile against the live withdrawn stub
`Sheaf.Paper.FinitePerfectQuotientModels`: the public predicates and coefficient
interface used in its signature were absent. I therefore adapted that unclaimed
module in the same delivery. It now restores the interface declarations needed by
the assigned theorem (`finiteModelConstantComplex`, `FinitePerfectModelsOn`,
`HasUniformFinitePerfectModels`, `FinitePerfectModelsNormalized`,
`FinitePerfectModelsCompatible`, and the proved normalization compatibility
lemma), together with their supporting instances and imports. The successor
induction theorem and its consumer theorem remain out of this packet because they
are not used by the assigned module and restoring their archived `sorry` would
reintroduce the exact stage-3 gate failure returned on the previous delivery.

## Proved and sorry left

The assigned theorem
`AlgebraicGeometry.Scheme.finitePerfectModels_adic_realization` remains one
`sorry` (node `lem-weil-pbc-finite-perfect-adic-realization`); it is the item being
restored and was not proved in this repair. The adapted quotient-model module has
zero `sorry`s. No new theorem or split-off node was added, and no definition
contains `sorry`.

## No longer needed

The seven imports of the withdrawn quotient stub are no longer needed as direct
imports of `Sheaf.Paper.FinitePerfectQuotientModels`:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.ProEtaleConstructibleSheaf`

The archived declarations `residuePerfect_quotient_models_succ` and
`residuePerfect_finite_quotient_models` are not needed by the assigned theorem and
are deliberately left for the node's future proving item. No DAG node was removed
or changed; the existing successor node remains attached to its original module.

## Where the brief, the DAG or earlier work was wrong

The returned delivery correctly identified that the assigned source had been
quarantined, but its full restoration also restored
`residuePerfect_quotient_models_succ := by sorry` from a module that is currently a
withdrawn stub. The stage-3 gate then counted a second `sorry` (1 to 2) and rejected
the repair. The minimal public interface above is sufficient for the assigned
module, compiles, and leaves the separate successor obligation untouched.

## Forced adaptations

`Sheaf.Paper.FinitePerfectQuotientModels` was unclaimed. Against the original live
stub, the assigned file failed at line 83 with `unknown identifier
FinitePerfectModelsCompatible` (and likewise could not resolve
`HasUniformFinitePerfectModels`). The adapted file changes only that module: it
replaces the withdrawn stub with the required declarations and their supporting
imports/instances. The assigned file itself is unchanged from quarantine. This is
the minimum adaptation required for the restored signature to compile.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
