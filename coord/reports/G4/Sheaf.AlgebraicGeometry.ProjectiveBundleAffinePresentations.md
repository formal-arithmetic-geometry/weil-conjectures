## What changed

Proved `AlgebraicGeometry.exists_affine_projectiveBundle_presentations` in
`Sheaf.AlgebraicGeometry.ProjectiveBundleAffinePresentations`, with its statement,
universes, visibility and public imports unchanged. Added proved private helpers
for restriction of finite generators, padding with a zero generator, affine
section generation, and a natural graded polynomial presentation.

The proof explicitly evaluates polynomial variables at the chosen symmetric
sections. Affine cokernel-image exactness makes evaluation on sections surjective;
span induction and symmetric-algebra induction make the polynomial map surjective.
The existing affine polynomial equivalences identify its source with the relative
projective-space algebra. Relative Proj functoriality and the existing free-bundle
comparison then supply the required closed immersion over the base and its
H-projective factorization. No arbitrary existence witness defines data.

Added private proof imports of
`Mathlib.AlgebraicGeometry.Modules.Tilde` (restriction quasi-coherence),
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`
(the proved free-module quasi-coherence instance),
`WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage`,
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf`,
`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`, and
`Sheaf.AlgebraicGeometry.FreeProjectiveBundleBaseChangeSpace`.
Updated the item's DAG proof, proof dependencies, proof origin, and obsolete tool
approvals to match this route. No other existing module or node was changed.

Edge cases: a finite generating family, including an empty family for the zero
module, is always padded by a zero section; the index type of the covering is the
point type of the base, so the empty base is covered without a special assumption.
Ranks may vary and no quasi-compactness or uniform bound is used.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.exists_affine_projectiveBundle_presentations`
(node `lem-trf-projective-bundle-affine-presentations`).

Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No split-off statements or new modules. The complete proof compiled without
errors or warnings through `lcompile.py` in 50.3 seconds before the final smaller
proof-import cleanup; delivery checks compile the final version again. The first
delivery probe caught missing Mathlib quasi-coherence instances after replacing
the source Tilde import; both the Mathlib Tilde import and the source free-module
instance import are now included explicitly. The proof uses the existing stated
`AlgebraicGeometry.RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace`;
its pre-existing hole remains in its own module and is not claimed as proved here.

## No longer needed

The following planned dependencies are unnecessary for this proof:

- `lem-trf-symmetric-sheaf-map-degreewise-surjective`
  (`Sheaf.AlgebraicGeometry.SymmetricSheafMapDegreewiseSurjective`): direct polynomial
  evaluation on affine section rings supplies the actual graded surjection.
- `lem-weil-pbc-module-pullback-quasi-coherent`: Mathlib directly preserves
  quasi-coherence under open restriction.
- `lem-weil-pbc-open-immersion-module-pullback-restriction`
  (`Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`): restriction is used
  directly, with no tensor-pullback comparison.
- `lem-weil-pbc-quasi-coherent-finite-type-affine`
  (`WeilConjectures.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`): finite type
  follows from the finite generating family, and the proved source-library free-module instance supplies
  quasi-coherence without that general finite-presentation theorem.

Removed the last two listed module imports from the working proof. Replaced the
working `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde` import by its
smaller `Modules.Sheaf` dependency, which supplies the finite free biproduct and
over-category unit comparison used here, and Mathlib
`AlgebraicGeometry.Modules.Tilde` for restriction quasi-coherence, plus the source sheaf
`Quasicoherent` extension for free modules. The other
planned modules were never imported. Removed the obsolete top-level `tool_uses`
approvals for `lem-weil-pbc-module-pullback-quasi-coherent` and
`lem-weil-pbc-quasi-coherent-finite-type-affine`; retained the relative-Proj approval.
These are dependency removals for this item's proof, not withdrawals of existing
modules or declarations. The blueprint unit's route and statement remain intact.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The planned sheaf symmetric-algebra
surjection is more general than needed. The existing relative-Proj API consumes
surjective affine-section graded algebra maps directly, and the relative
projective-space polynomial equivalences and their restriction equation provide
exactly the needed source. This yields the proof without a new comparison theorem
between two free symmetric-algebra interfaces.

During compilation, the explicit polynomial presentation was made irreducible with
proved coefficient and variable equations to avoid expensive unfolding. This is a
new private definition within this module; no shared interface or importer was
changed. All its data are the explicit polynomial evaluation construction.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
