## What changed

Proved `CategoryTheory.roosConeCompositorDescent` with its original signature and public
definitions. Private helpers construct canonical product comparisons, verify signed
cone coordinates and strict compositor equations, and descend the comparison through
fully faithful precomposition with derived localization. Normalization follows from
`strictRoosDerivation` and uniqueness of right derived functors.

Repaired both duplicates reported for returned head `4624e3fe2`: removed the private
`RoosCompositor.limit_unit_iso` and `RoosCompositor.roos_tower_grothendieck`, together
with the unused `ordinaryLimitIso` and `normalized_inclusion`. The existing private
`CategoryTheory.roos_inclusion_quasiIso` in `Sheaf.CategoryTheory.StrictRoosDerivation`
already proves the needed inclusion result for every K-injective tower. A private
`import all` of that module permits direct reuse without changing any dependency.
Only the coefficient category needs its existing Grothendieck instance.
Synchronous elaboration and explicit composed equality proofs avoid expensive
repeated conversion during the signed cone compositor calculation. Coordinate
constructions become locally irreducible after their proved equation lemmas.

Updated proof step 6 and its explanation to this shorter argument. No new node,
statement repair, definition repair or consumer adaptation is required.

## Proved and sorry left

Closed the one original hole: `CategoryTheory.roosConeCompositorDescent`
(node `lem-trf-roos-cone-compositor-descent`). Holes added: zero. Split off: zero.
There are zero remaining `sorry` occurrences in the delivered Lean module; every
private helper has a complete proof.

Validation: the full repaired module compiled through `lcompile.py` in 54.6 seconds
with no warnings or errors. The import/duplicate-statement checker also passes. Text comparison
against current source confirms every original public definition, public import and
the main theorem signature is unchanged. Every Lean line has at most 100 characters.

## No longer needed

The proof does not apply `CategoryTheory.strictRoosComparison`
(node `lem-weil-strict-roos-comparison`) or `CategoryTheory.exactProductFunctorStrictLimit`
(node `lem-cbc-exact-product-functor-strict-limit`). The strict derivation universal
property supplies normalization and localization of the signed cone map supplies the
comparison. Removed those nodes from `proof_deps` and withdrew their top-level
`tool_uses` approvals. Their original public imports remain part of the module
interface. Neither dependency module is withdrawn.

Removed the two duplicate private theorem proofs and their unused helpers described
above. Their direct proof imports are no longer needed:
`Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives`,
`WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit`,
`Mathlib.CategoryTheory.Adjunction.Evaluation`, and
`Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory`, and
`Mathlib.Algebra.Homology.DerivedCategory.KInjective`.
`Sheaf.Paper.ExactProductFunctorRoosResolution` was explored during repair but is
unnecessary because `roos_inclusion_quasiIso` proves the needed result directly.
No library module is pruned or withdrawn and no existing library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The returned packet reproved two existing private theorems. The repair eliminates
both arguments by reusing the stronger, already proved inclusion theorem from the
strict derivation module. That theorem has no injective-term assumption. The original
proof step 6 used a stronger single-functor comparison; normalization instead follows
from the strict derivation universal property. The signed product/cone calculations
and localization descent retain the unit route.

The change record `coord/changes/F4-roos-cone-compositor-proof-helpers.md` records the
private command-level additions, unchanged public interface and zero Lean consumers.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
