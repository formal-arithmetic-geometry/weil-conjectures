## What changed

Proved `AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed` in
`Sheaf.AlgebraicGeometry.OpenClosedRecollement`, preserving its complete signature and the
three public imports. No definition, instance, public signature, or consumer changed.

The proof adapts the existing cone argument in
`WeilConjectures.SixFunctors.OpenClosed.Derived.exists_distTriang_openClosed` directly to
D⁺ and the exact closed direct image. The open unit and closed counit remain the specified
levelwise derived adjunction maps. The sheaf short exact sequence, with its actual counit
and unit, gives joint conservativity by the short five lemma; homology transports that
criterion and the two vanishing statements to D⁺. The cone is then identified with the
closed term by its unit, with a proved equality identifying the second arrow.

Naturality follows for every derived morphism from
`CategoryTheory.Pretriangulated.triangle_morphism_extension`: the closed adjunction and
closed restriction of extension by zero give the required vanishing Hom group. This avoids
choosing arbitrary cone morphisms or merely asserting that representatives are compatible.
The proof-only import of that theorem replaces the unused complex-SES and localization glue.

The original DAG node's proof, proof dependencies, proof origin, and obsolete tool approvals
are updated to match this proof. No new nodes or auxiliary holes are introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed`
(node `lem-cbc-open-closed-recollement`).

Holes added: 0. Holes left in the delivered Lean module: 0. Split-offs: 0.
This is a proof, not a decomposition. Server single-file compilation passed with no errors or warnings (15.8 seconds).
`#print axioms AlgebraicGeometry.Etale.exists_functorial_distTriang_openClosed` reports
exactly `propext`, `Classical.choice`, and `Quot.sound`; in particular no `sorryAx` is reachable.
The diagnostic print command was removed after verification. Import direction and the
updated DAG were checked for cycles; every recorded proof dependency exists and none
reaches this item.

## No longer needed

Removed proof-only imports:

- `Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.
- `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`.
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`.
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (available through
  existing public imports).
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs` (available through the
  existing public derived-open import).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (already reexported by the retained
  public `Sheaf.AlgebraicGeometry.DerivedCategories`).
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`.
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`.

The proof does not need the declared nodes
`lem-weil-pbc-module-sheaves-colimits-forgetful`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-exact-functor-derived-functor`, or
`lem-weil-pbc-complex-ses-triangle`. The first two concern a coefficient-forgetting or
SheafOfModules interface: the actual `Sheaf ... (ModuleCat Λ)` operations already supply
the exactness instances used by this statement. The general derived-functor comparison and
complex-SES construction are unnecessary because the levelwise functors and adjunctions are
already constructed, and the cone argument identifies the exact maps directly. All three
obsolete top-level `tool_uses` entries are removed in their existing order.

The sheaf short exact sequence is retained and explicitly used. Its
`WeilConjectures.SixFunctors.OpenClosed.Exact` module remains imported. The exact-functor
homology/bounded-below API, extension-by-zero exactness and adjunction, and finite
pushforward exactness are still used and are not claimed as pruned. No globally unused
module is withdrawn; these are local import/dependency removals only.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The earlier DAG prescribed a longer route through
a degreewise short exact sequence, its connecting map, and localization naturality. The
source library already contains the shorter cone-identification argument; the present proof
adds its bounded-below exact-adjunction version and full naturality. The unit's sheaf short
exact sequence and specified adjunction arrows remain explicit inputs. The unit record has
empty `realized.statement` and `realized.steps`; no separately realized unit node is bypassed.

The three Sheaf coefficient/derived comparison interfaces imported previously are unnecessary
for the encoding used here. No incompatible statement was applied or repaired.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
