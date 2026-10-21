## What changed

Completed `SheafOfModules.site_one_sided_tensor_normalization` with its original signature.
The proof transports quasi-isomorphism preservation from the existing fixed-tensor theorem
through the supplied `hB`, constructs the comparison by fully faithful localization
precomposition, proves its exact normalization, and proves uniqueness and naturality in the
fixed factor by cancellation at a flat-term K-flat resolution. The same argument applied to
flipped bifunctors gives the reversed order. The signed summand equation is the existing
`CochainComplex.Monoidal.ι_braiding_hom` theorem.

Added proved private helpers `extend_comparison` and `resolving_trans_ext` for the
localization extension and resolution cancellation, and `uncurry_map_left` and
`uncurry_map_right` for the generic bifunctor identity-map equations. The generic equations
avoid unfolding the concrete sheaf tensor construction during identity simplification. Added the proof-only import
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients` for the existing
`siteSheafTensorRightIso` comparison that identifies the resolution theorem's flatness
clause with `IsFlatOnSite`. Updated the item's DAG proof and dependencies to this argument.
All public imports, definitions, statement hypotheses, universes and conclusions are preserved.
The added fixed-tensor dependency is used as a general tool, specifically its preservation
clause. LeanFinder and Loogle searches located the generic localization-extension API;
local searches located the existing fixed-tensor and signed-braiding declarations.

## Proved and sorry left

Closed the one original hole: `SheafOfModules.site_one_sided_tensor_normalization`
(node `lem-trf-site-one-sided-tensor-normalization`). Its module now has zero holes.
Added zero holes, split off zero statements, and left no unfinished private proof.
This is a proof from existing declarations, including the already stated
`SheafOfModules.KFlatFixedTensor.kFlat_fixed_tensor_triangulated`; its existing hole is
unchanged. No dependencies are claimed to have been proved by this delivery.

## No longer needed

Removed the proof-only imports
`WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic` and
`WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone`.
The proof does not reconstruct the cone calculation; it uses the existing fixed-tensor
preservation clause. Accordingly, removed the direct proof-dependency edges and obsolete
`tool_uses` entries for `lem-pur-quasi-iso-cone-acyclic` and
`lem-pc-tensor-mapping-cone-iso`. Removed the direct proof edge to
`def-weil-sheaf-of-modules-category` and `def-pc-kflat-complex`, which remain statement
dependencies.
The cone nodes and modules may still be needed transitively by the fixed-tensor theorem;
no global module withdrawal is requested. All remaining original proof dependencies are used.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The node's cone argument is already
available in the imported fixed-tensor theorem, so repeating it here is unnecessary.
The resolution theorem expresses termwise flatness using the monoidal tensor-right functor;
the proved `siteSheafTensorRightIso` supplies the exact bridge to this item's site-flatness
predicate. The updated dependency list records this bridge and the fixed-tensor theorem.
The fixed-tensor theorem does not reach this item's node, so this route creates no DAG cycle.
The unit's statement and realized route are preserved; no unit realization is bypassed.

## Second reading by R6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
