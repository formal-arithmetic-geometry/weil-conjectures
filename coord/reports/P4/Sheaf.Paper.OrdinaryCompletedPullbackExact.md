## What changed

Filled `WeilConjectures.OrdinaryImmersionChart.ordinaryCompletedPullbackExact` in
`Sheaf.Paper.OrdinaryCompletedPullbackExact`, preserving its full signature and
its public import of `OrdinaryImmersionChartModels`. All added imports are private
proof imports; all added helpers are private and proved. No other existing Lean
module, definition, instance, statement or public interface was changed.

The coefficient argument works at `max u (t + 1)` without identifying the scheme
and coefficient universes. It transports finite constant representability through
ULift, reuses the finite-test-object construction and its geometric limit, and
shows inverse image preserves the finite ring tower limit. The actual completed
coefficient sheaf is a limiting cone, as verified by forgetting commutativity to
its defining RingCat limit. Constant comparisons are invertible by the constant
sheaf adjunction. The projection equations for `completedRingMap` make it a
morphism of these limiting cones, proving that specific structural map invertible.

Its unit and the canonical forgetful comparison supply the ring unit presentation
needed by the general-universe module inverse-image adjunction. The underlying
abelian inverse image preserves finite limits by flatness and filtered-colimit
exactness. Forgetting modules reflects these limits, giving the stated result.
The item's node now records this route and its actual dependencies. The unit's
statement and steps are unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.OrdinaryImmersionChart.ordinaryCompletedPullbackExact`
(node `lem-tw-ordinary-completed-pullback-exact`).

Holes closed: 1. Holes added: 0. Holes remaining in the delivered module: 0.
No statements were split off. All auxiliary lemmas and constructions have complete
Lean proofs or actual constructed data.

Validation: the complete module compiled on the project server in 22.0 seconds,
including the import cleanup. `#print axioms` for the item theorem reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The temporary print command was
removed for delivery. The theorem's signature was checked verbatim against the
shared source; all lines are at most 100 characters.

## No longer needed

No original imports were removed: the original public model import remains.
Removed redundant trial proof imports, all already in that model's public import
closure: `Mathlib.CategoryTheory.Sites.PreservesLimits`,
`WeilConjectures.Mathlib.CategoryTheory.Functor.Flat`,
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types`,
`Mathlib.Algebra.Category.Grp.AB`,
`Mathlib.Algebra.Category.Ring.FilteredColimits`,
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf`.
The following planned dependencies are not needed for this item's proof:

- `lem-weil-pbc-standard-quotients-perfect`, module
  `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`: only finiteness
  of the actual extension coefficient quotients is needed; use the already proved
  `Padic.finite_coefficientExtensionRing` directly. No perfectness is used.
- `lem-weil-pbc-profinite-coefficient-inverse-image`, module
  `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`: its attached theorem
  fixes coefficients in the successor of the scheme universe. Prove the required
  independent-universe instance using the existing lower finite-representation
  construction, ULift comparisons and canonical projection equations. Neither
  this wrapper nor `Sheaf.AlgebraicGeometry.ProEtaleFiniteTowerLimit` is imported;
  their lower geometric ingredients remain needed and are imported explicitly.
- `lem-weil-pbc-module-inverse-image-action-adjunction`, module
  `Sheaf.CategoryTheory.ModuleInverseImageAdjunction`: use the already proved
  general-universe `SignedLineModuleInverseImageAdjunction` instead, avoiding
  transport to coefficient-sized small site models.

These are removals from this node's planned route only. No module or declaration
is withdrawn, and no claim is made that other consumers do not need them.

## Where the brief, the DAG or earlier work was wrong

The planned mathematics is valid. Two listed wrapper declarations have narrower
universe conventions than this item's independent-universe statement. The proof
uses their existing geometric ingredients and the existing general-universe
module adjunction, respectively. The perfectness theorem is stronger than the
finite-set fact needed here. No statement repair or change record is required.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
