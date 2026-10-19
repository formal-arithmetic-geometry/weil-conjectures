## What changed

Proved `AlgebraicGeometry.Scheme.isGloballyGeneratedEtaleSheaf_iff_geometricStalk_surjective`
in `Sheaf.AlgebraicGeometry.GlobalGeneratedStalkwise`, with its signature unchanged.
The forward implication uses the skyscraper adjunction and the module epi/surjective
criterion. The reverse implication uses the existing conservative family of lifted
algebraic-closure points, joint reflection of epimorphisms for module sheaves, and
naturality of `uliftSheafFiberIso`. Explicitly shrink module-category limits to fix
the skyscraper adjunction's coefficient-universe inference.

Updated the theorem docstring and node proof, proof dependencies and proof origin
to this shorter route. No definitions, statements or public imports changed. The
unit realization has no statement or steps assigned to this auxiliary node, and no
unit route is bypassed. The theorem compiled cleanly through `lcompile.py` (3.5 s).
Edge cases need no additional hypotheses: the conservative-family argument covers
empty schemes, and the module epi criterion covers the zero ring and zero sheaf.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isGloballyGeneratedEtaleSheaf_iff_geometricStalk_surjective`
(node `lem-kun-global-generated-stalkwise`). Added 0 holes. Left 0 holes in the
item and introduced no other modules or declarations. This is a proof, not a
decomposition.

## No longer needed

Removed proof imports:
- `WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful`
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits`
- `Mathlib.CategoryTheory.Preadditive.Basic`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.AlgebraicGeometry.PointedEtaleStalk`

The declared dependencies `lem-weil-pbc-module-sheaves-colimits-forgetful`,
`lem-weil-pbc-preadditive-epi-iff-cokernel-zero` and
`prop-weil-pbc-geometric-stalks-exact` are unnecessary for this proof: Mathlib's
joint reflection of epimorphisms handles module sheaves directly, so no scalar
forgetting, explicit cokernel, or exact-stalk reduction is needed. Withdrew the
obsolete top-level `tool_uses` approval for
`lem-weil-pbc-module-sheaves-colimits-forgetful`. The geometric stalk definition,
global-generation definition and geometric conservative-family node remain used.
The listed module removals describe this theorem's direct dependencies; they do
not assert these modules disappear from every other target's import closure.

## Where the brief, the DAG or earlier work was wrong

The original three-step plan is valid but longer than the available library API
requires. The library already applies joint reflection of epimorphisms to module
sheaves in its finite-pushforward proofs; this supplies the shorter route here.
No false statement, definition defect, or tool failure was found. No new nodes.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
