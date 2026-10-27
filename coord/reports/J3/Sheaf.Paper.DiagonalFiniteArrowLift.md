## What changed

Proved `AlgebraicGeometry.ProEtale.diagonal_finite_arrow_lift` without changing
its statement or either existing proposition definition.

Added the proved factorization theorem
`AlgebraicGeometry.ProEtale.diagonal_residue_derived_factorization` in
`Sheaf.Paper.DiagonalResidueDerivedFactorization`. Its proof constructs ordinary
residue reduction using the source library's sheafified quotient functor, then
compares universal derived functors on a common class of regular complexes.
It reuses the proved cochain and regular-complex helpers of
`Sheaf.Paper.DiagonalDerivedReductionExists` through a proof-only `import all`.

The assigned module privately imports the new factorization module and
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and proves
private pure-object lifting and Ext-transport lemmas. The factorization module's
other proof import is
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Reduction`.
Local irreducibility annotations keep scalar-extension and Ext definitions from
expanding during elaboration; no exported interface or global attribute changes.
Exact coefficient restriction reflects cohomological concentration. Its fullness
and faithfulness on the hearts therefore lift the prescribed source and target
isomorphisms. Applying the residue derived functor to the given arrow and
conjugating by these isomorphisms yields the required Ext class. Naturality proves
the exact displayed restriction equation. There is no claim that coefficient
restriction is full on arbitrary derived morphisms.

Validation: the server accepted the complete proof. The residue-factorization
module compiled in 46.6 seconds and the assigned module in 34.5 seconds. The
final packet removes all profiler options and the one reported redundant tactic.
Existing declaration signatures and both proposition bodies were compared with
the shared source and are unchanged. No direct importer adaptation is required.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.diagonal_finite_arrow_lift`
(`lem-sfb-diagonal-finite-arrow-lift`).

The new theorem
`AlgebraicGeometry.ProEtale.diagonal_residue_derived_factorization`
(`lem-sfb-diagonal-residue-derived-factorization`) is fully proved.

Holes closed: 1. Holes added: 0. Holes remaining in delivered Lean files: 0.
No split-off sorry statements and no hollow definitions.

## No longer needed

No existing import was removed: the assigned module originally imported only
`Sheaf.Paper.CanonicalSheafExt`, which its statement still needs. All added proof
imports are private.

The original planned dependencies below are unnecessary for this proof:

- `lem-weil-pbc-site-module-sheaf-constant-ring-equivalence`
  (`Sheaf.CategoryTheory.SiteModuleSheafConstantRingEquivalence`): direct fixed-scalar
  sheaf quotient construction replaces transport through ringed-site categories.
- `lem-pc-kflat-resolution`
  (`Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`):
  the existing flat-term source resolution and regular
  resolving-class helpers suffice; the separate planned K-flat statement is unused.
- `lem-pur-constant-two-term-resolution`
  (`Sheaf.Paper.ConstantTwoTermResolution`): quotient short exact sequences and
  monic prime-power multiplication replace a separate coefficient resolution.
- `lem-pur-derived-change-of-rings`
  (`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`):
  the regular-class cochain construction and
  the derived universal property give the factorization directly.
- `def-kun-truncations`
  (`Sheaf.CategoryTheory.TruncationsAndHomotopyColimits`):
  Mathlib's derived t-structure single-object recognition
  and exact-functor concentration reflection provide pure-object lifting.

These nodes are removed only as direct planned proof dependencies. Of the five
modules, only `Sheaf.Paper.ConstantTwoTermResolution` is absent from this item's
Lean import closure. The constant-ring equivalence, independent-coefficient
K-flat resolution, ordinary derived change of rings, and truncation modules remain
transitively imported by the preserved coefficient interface or reused derived
construction. They are not claimed as globally pruned. No upstream declaration
or module is withdrawn, and no existing proved body is replaced by a hole.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The DAG's residue-factorization
plan was longer than necessary: existing strict-reduction regular-complex machinery
already supplies the required computation and universal comparisons. The counit
normalization hypothesis on the source is not needed by the proof, but is kept
verbatim in the public statement.

## New nodes

`lem-sfb-diagonal-residue-derived-factorization`, realized by the fully proved
`Sheaf.Paper.DiagonalResidueDerivedFactorization`. This is only the functor
factorization step: it has no endpoints, Ext class, or lifting conclusion. The
remaining pure-object lifting and Ext-transport argument is proved in the assigned
module. The new theorem introduces no hole.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
