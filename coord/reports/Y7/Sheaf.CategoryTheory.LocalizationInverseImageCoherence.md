## What changed

Proved five original holes in `Sheaf.CategoryTheory.LocalizationInverseImageCoherence`.
The localization unit is the sheafification of the explicit map m ↦ m ⊗ 1.
Exactness uses the existing geometric inverse-image exactness theorem after an
explicit universe-presentation conversion; scalar localization is exact by flat
sectionwise tensor and monoidal sheafification. The generalized fraction formula
uses the algebraic inverse-image graph equations, including exponent zero.
The derived unit equation follows by localizing arbitrary natural transformations
and proving the required whiskering equations privately. Localized-scalar full
faithfulness follows from ordinary localization linearity and descent along the
locally surjective ring-sheafification unit.

The proof-context change record is
`coord/changes/localization-inverse-image-coherence-proof-options.md`. The checker
requires independent review of the elaboration commands and private helper context.
All public statements, definitions, universes and visibility are unchanged. New
helpers are private and fully proved. Updated the existing node's proof and
proof dependencies to describe these arguments. No consumer adaptation is needed.
The source compiles cleanly through lcompile.py (41.1 seconds after import pruning).

## Proved and sorry left

Closed five of the seven holes in the current shared-source baseline:

- `CategoryTheory.existsUnique_scalarLocalizationUnit`.
- `CategoryTheory.localization_inverseImage_exact`.
- `CategoryTheory.localizationInverseImage_fraction`.
- `CategoryTheory.localizationComparisonDerived_unit`.
- `CategoryTheory.localization_restrictScalars_fullyFaithful`.

Two original holes remain, with their original statements and complete proof
sketches, both under `lem-weil-pbc-localization-inverse-image-coherence`:

- `CategoryTheory.existsUnique_localizationInverseImage`.
- `CategoryTheory.existsUnique_localizationInverseImageRing`.

Actual hole count: 2. Holes added: 0. Split-offs: 0. This is a partial proof delivery,
not a claim that the module comparison or ring comparison has been proved.
The five coherence theorems already proved in the shared source are retained.

## No longer needed

No modules or nodes withdrawn. Removed these direct proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor`:
  the completed exactness proof uses the monoidal sheafification API instead.
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects` and
  `Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects`: the completed fraction
  clause uses the graph fields directly. These are still part of the plan for the
  unproved ring comparison.
- `Sheaf.CategoryTheory.GeometricModuleTransport`,
  `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`,
  `Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair`, and
  `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`: the completed exactness
  clause instead uses `Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`.
  GeometricModuleTransport remains in the plan for the unproved module comparison.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`: the completed derived unit
  calculation uses the existing exact derived factorization and localization API.
- `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `Mathlib.Algebra.Module.LocalizedModule.Exact`, and
  `Mathlib.RingTheory.Localization.BaseChange`: the completed proofs use flatness
  and `Mathlib.RingTheory.Localization.Module` for extension of linear maps.

The independent-coefficient tensor comparison is used only to identify the explicit
site tensor with the existing monoidal tensor. Its node
`lem-weil-pbc-independent-sheaf-tensor-colimits` is recorded in proof dependencies.
The existing `lem-trf-geometric-inverse-image-exact` is used as a general theorem
about arbitrary normalized module inverse-image presentations; it supplies exactly
the exactness clause needed here. Its proof dependency is recorded for independent
review. The remaining unproved comparisons retain their original dependencies and
are not counted as pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox report was stale: the unit, exactness and full-faithfulness
proofs now pass whole-file compilation. The old direct Sheaf sheafification-tensor
import was retired upstream; the final proof does not require that direct import.
The derived unit argument needs functoriality for arbitrary natural transformations,
whereas the existing coherence API states it for natural isomorphisms. The required
versions are proved privately from the localization factorization equations.

An exploratory sequential-colimit argument did not finish and is excluded from the
delivery source; it added no declarations or holes to this packet. The remaining
module and ring comparison holes are the original unresolved universal-property
arguments, not newly introduced subgoals.

The dispatcher's reference metadata was reset across interrupted continuations:
the retained earlier record began at 1792425880.560168, whereas the current .budget
begins at 1792435955.0069115. Neither file was edited by this worker. No clock check
is needed for this packet because it adds no holes.

## Second reading by Y7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
