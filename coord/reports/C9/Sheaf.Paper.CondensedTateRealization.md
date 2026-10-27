## What changed

Filled seven original theorem holes in `Sheaf.Paper.CondensedTateRealization`.
The proofs use Mathlib's finite-module ULift instance, inherited monoid-homomorphism
instances, multiplication of natural-number scalars, and equivalence additivity.

Scoped removal of the generic essentially-small sheafification instance makes these
constructions use the same pro-etale sheafification as the completed-limit API.
Local irreducibility prevents expansion of generic derived functors. The lifted
normed field uses fast_instance% on the same induced structure, and its normed
algebra uses the existing canonical instance. Derived augmentation is still the
same adjunction transpose of the actual cone, expressed with explicit local source
and target functors to avoid repeated comparisons between category aliases.
`CompletedRing` is now a regular definition with its identical completion body,
so elaboration does not unfold the limit automatically. `rationalToQbar` records
its existing source and target explicitly. Strict transparency options and local
canonical instances keep derived-category elaboration bounded. The actual rational derived
extension is named once and reused. The scalar shift is inherited from its
derived restriction adjunction.
No mathematical theorem statement or public import changes.

See `coord/changes/condensed-tate-local-transparency.md` for the definition and
elaboration record. No current Lean consumer requires adaptation; DAG parents and
the unit route remain intact.

## Proved and sorry left

Seven of fourteen original holes closed; zero holes added or split off.
All names below are in `AlgebraicGeometry.ProEtale.CondensedTateRealization`.

Proved:

- `liftedQ_finite`
- `integralToRational_isMonHom`
- `rationalToQbar_isMonHom`
- `finiteUnit_square`
- `integralEncoding_additive`
- `integralEncoding_inverseAdditive`
- `integralToQbar_isMonHom`

Sorry retained, each with the original node `lem-pur-condensed-tate-realization`:

- `rationalToQbar_preservesFiniteLimits`
- `integralComparison_existsUnique`
- `powerProjection_compatible`
- `augmentation_compatible`
- `balancedPower_existsUnique`
- `encodedBalancedPower_existsUnique`
- `condensed_tate_realization`

The main theorem is not claimed proved or decomposed. This is a partial delivery
of a module with several holes, as allowed by the brief.

## No longer needed

Removed private imports unused by the completed proofs and existing constructions:

- `Sheaf.Paper.CondensedZlReduction`
- `Sheaf.Paper.CompletedConstantSheafReduction`
- `Sheaf.AlgebraicGeometry.ProEtaleReplete`
- `Sheaf.Algebra.Homology.KFlatTelescopeClosure`
- `Sheaf.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.ChangeOfRingsKFlat`

No modules or DAG nodes are withdrawn: these are planned inputs to the unfinished
main proof, whose original unit route and dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

No false statement or unit-route departure was found. Earlier experiments at
projection compatibility, scalar exactness and the balanced family were not
included. Full diagnostic runs identified expensive kernel comparisons of derived
categories with different inferred sheafification and category aliases. The
scoped sheafification correction, bounded completion alias and explicit local
functors address those comparisons. The final single-file compile passed in 57.9 seconds. Delivery validation follows.
No timeout is reported as a broken tool.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
