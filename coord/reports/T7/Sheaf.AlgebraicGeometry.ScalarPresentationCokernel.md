## What changed

Proved `AlgebraicGeometry.ProEtale.scalar_presentation_cokernel` with its full original
statement. The proof reuses the proved private `scalarFreeIso`, `scalarMatrix_map`, and
finite-colimit/additivity instances from `FiniteConstantLocalModel` through a private
`import all`. Naturality of the extension-restriction unit proves the specified basis
normalization. Mathlib transports the image of the specified cokernel cofork along the
free comparisons and supplies its unique comparison to the chosen cokernel. Updated
`lem-sfb-scalar-presentation-cokernel` to record this shorter internal-module argument.
No definition, public signature, visibility, or public import was changed.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.scalar_presentation_cokernel` (node
`lem-sfb-scalar-presentation-cokernel`). Zero holes remain in the item; zero holes added;
zero statements split off. This is a proof, not a decomposition.

## No longer needed

Removed these proof imports:

- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf`
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.InternalSectionTensorComparison`
- `WeilConjectures.CategoryTheory.ModuleObjects.Monoidal`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.CategoryTheory.Adjunction.Limits`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`

The direct internal-module proof no longer uses these planned proof dependencies:
`lem-weil-pbc-sheaf-tensor-closed`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-pe-internal-section-tensor-comparison`, `def-sfb-modobj-relative-tensor`,
`lem-cbc-sieve-module-sheafification`, `lem-weil-pbc-ringed-topoi-module-adjunction`,
`def-pur-sheaf-tensor-product`, and `lem-pc-sites-sheaf-tensor-bilinear-universal`.
`sk-def-sfb-pulled-back-coefficients` and `def-sfb-finitely-presented-module` remain
statement dependencies but need no separate proof steps. The local-model construction
already supplies the functor and free/matrix comparison, so no sectionwise tensor
comparison, second sheafification, or ringed-topoi bridge is needed here. Removed the four obsolete maintainer `tool_uses` entries:
`lem-weil-pbc-sheaf-tensor-closed`, `lem-pe-internal-section-tensor-comparison`,
`lem-weil-pbc-ringed-topoi-module-adjunction`, and
`lem-pc-sites-sheaf-tensor-bilinear-universal`. This removes
these dependencies from this node only; no global withdrawal is claimed.

## Where the brief, the DAG or earlier work was wrong

The six-step DAG plan is mathematically valid but repeats work already fully proved
in `FiniteConstantLocalModel`. Its `scalarMatrix_map` uses the same `scalarFreeIso`
required here, and the scalar-extension functor already preserves finite colimits.
The canonical regular-extension isomorphism has the needed unit normalization, so
neither constructing sectionwise balanced pairings nor transferring module categories
is necessary. The unchanged conclusion includes arbitrary specified quotient arrows,
all matrix entries, and the rank-zero cases (empty basis and empty biproduct).
The blueprint unit and its route are unchanged. No new nodes or change records.

## Second reading by T7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
