## What changed

Proved `AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint` in
`Sheaf.AlgebraicGeometry.ProEtaleRingedClosedKernelAdjoint`. All existing public
statements, definitions, visibility and public imports are unchanged. No other Lean
module is changed.

The support kernel is evaluated pointwise, killed by exact open inverse image, and
identified with its closed direct image by the open-closed exact sequence. Kernel
factorization and full faithfulness of closed direct image give the ordinary
adjunction and its specified counit. The open ordinary counit follows from the
adjoint triple, using fully faithful extension by zero.

Private proved helpers implement these arguments and the derived calculations.
Exact adjunctions descend by `Adjunction.localization`; the two right-derived
adjunctions use the existing source-library
`Adjunction.mapDerivedCategoryRightDerivedAdjunction`. The proof computes its
counit on K-injectives and transports it along an arbitrary resolution. Homology
comparison proves the derived open restriction of closed direct image is zero.
The existing node's proof, proof dependencies and proof origin follow this route.

Added proof imports: `import all` of the existing ringed open-closed module (for
its actual module inverse/direct-image adjunction), Mathlib adjoint triples,
preservation of kernels, localization of adjunctions, and the source-library
right-derived adjunction. The private helpers realize the existing node's proof
steps; they introduce no separate mathematical assumptions or public results.

Validation: the full cleaned module compiles without warnings (47.7 seconds).
Projection-based extraction of the two existential packages avoids expensive
elimination into the large dependent conclusion. No compilation limit was raised.
The construction works unchanged for empty closed or open complements and the
zero coefficient ring; it assumes neither boundedness nor constructibility.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtale_ringed_closed_kernel_adjoint`
(node `lem-sf-ringed-closed-kernel-adjoint`). Added 0 holes. There are no remaining
`sorry`s in the delivered module, and every private helper is proved. This is a
proof, not a decomposition into new unproved statements.

## No longer needed

Removed these direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`
- `Sheaf.AlgebraicGeometry.RingedTopoiModuleAdjunctionRepair`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`

Removed the following direct proof dependencies and their obsolete top-level
`tool_uses` entries, retaining the order of the remaining approvals:

- `lem-weil-pbc-ringed-topoi-module-adjunction`: the actual module adjunction is
  already constructed in the ringed open-closed module.
- `lem-weil-pbc-proetale-ringed-open-comparison`: its equivalence is already in
  the open-closed package; the open counit follows from the adjoint triple.
- `lem-weil-pbc-exact-functor-derived-functor`: localize the termwise exact
  adjunction directly using the existing exact-functor comparison.
- `lem-weil-pbc-kinjective-total-derived`: use the existing source-library
  canonical right-derived functor and derived-adjunction construction.
- `lem-weil-pbc-right-adjoint-preserves-kinjective`: the source-library derived
  adjunction uses absolute derived functors and needs no separate application of
  K-injective preservation in this proof.
- `prop-pur-kinjective-resolutions-exist`: the operations interface already
  supplies the needed K-injective-resolution instances at the actual universes.

These are direct dependency removals, not withdrawals of those modules.
`ProEtaleInverseImage` and open comparison remain needed transitively by the
unchanged ringed open-closed construction; `RightDerivedFunctor.Comp` remains
imported by the unchanged source-library derived-adjunction module. No source
library declaration or module is removed or replaced by a hole. No unit statement
or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The mathematical statement and planned kernel argument are correct. The plan
unnecessarily repeated an open-counit calculation and the generic construction
of unbounded derived adjunctions. Existing source-library APIs supply the latter;
the adjoint-triple theorem supplies the former. The node now records the actual
proof and the explicit comparison calculations needed for the specified counits.
No definition repair, forced consumer adaptation, new node or statement change
was needed.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
