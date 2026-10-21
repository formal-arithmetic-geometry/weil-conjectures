## What changed

Completed all eight theorem proofs in `Sheaf.Paper.OpenScalarSiteCoherence`.
Scalar composition and identity follow from restriction pasting, exact derived
functor coherence, and uniqueness of adjunction mates. The scalar/site square
comes from the ordinary coefficient/site restriction cube, exact descent, and
two mate calculations. Its private helper proves the equation for arbitrary
inputs; the published statement and all its bounded-flat hypotheses stay intact.
Site composition and identity descend the existing ordinary coherence equations.
The flatness clause uses canonical constant-scalar coordinates and bounded-flat
independent-coefficient K-flatness.

Added the fully proved module `Sheaf.Paper.OpenScalarFlatModelRealization`.
Its theorem constructs the linear sheafification unit, proves it invertible by
its underlying additive map, and transports flatness. This is a separate
coordinate-realization lemma, not a renamed assertion of the item. Both modules
have compiled together without errors or warnings through `lcompile.py --all`.
The final item compile took 50.6 seconds, within the unchanged 60-second limit.
All existing public signatures, data bodies, attributes and public imports remain
unchanged. New imports and helpers in the item are private. The change record is
`coord/changes/F9-open-scalar-site-proof-context.md`.

## Proved and sorry left

Closed all 8 original holes, in namespace
`AlgebraicGeometry.ProEtale.OpenScalarSite`:

- `extension_flat_kflat`
- `scalar_site_square`
- `etale_scalar_comp`
- `etale_scalar_id`
- `proetale_scalar_comp`
- `proetale_scalar_id`
- `site_comp`
- `site_id`

Added holes: 0. Split-off unfinished statements: 0. Remaining holes in the item: 0.
The new theorem
`AlgebraicGeometry.ProEtale.OpenScalarFlatModel.finiteCoefficientRealization_flat`
is also proved, with zero holes. This is a proof from the library's declared
interfaces, not a claim that every transitive dependency is already sorry-free.

## No longer needed

Removed these private proof imports from the item:

- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.AlgebraicGeometry.OpenComparisonTensorNormalization`
- `Sheaf.AlgebraicGeometry.ProEtaleExtensionZero`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`
- `Sheaf.CategoryTheory.LocalizedModuleExactForSystems`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.KFlatRingedToposPullback`
- `WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`

The adjunction calculation replaces the explicit tensor-generator and model-level
square, so these old proof dependencies are not needed as steps of this proof:

- `lem-pur-site-restriction-module-adjunction-exact`
- `lem-weil-pbc-ringed-slice-extension-tensor`
- `def-pc-flat-sheaf-modules`
- `def-weil-pbc-extension-by-zero`
- `def-weil-extension-by-zero`
- `lem-pc-bounded-above-flat-kflat-site`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-ringed-pullback-preserves-kflat`
- `def-weil-pbc-site-comparison-morphism`
- `lem-sf-open-comparison-tensor-normalization`
- `def-weil-extension-by-zero-presheaf`
- `def-weil-presheaf-modules-sheafification`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-cbc-proetale-extension-zero`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-cbc-extension-zero-projection-formula`
- `def-pur-sheaf-tensor-product`
- `lem-pur-derived-change-of-rings`

Some remain statement dependencies, public imports, or dependencies of other
modules; this delivery does not withdraw them or remove any adopted upstream
declaration. In particular the ringed tensor comparisons still specify the
published maps, although the coherence proof uses their adjunction definitions.
The old off-route approvals not used by this route were removed from the node's
`tool_uses`; no approval was added, reordered or replaced.

No module is withdrawn. The unit statements and realized steps are retained.
The second node attachment `lem-pur-etale-open-scalar-composition` remains a
specialization of the unchanged composition and identity clauses; its proof
origin now records the implemented route.

## Where the brief, the DAG or earlier work was wrong

No existing mathematical statement needed correction. The original plan's
chain-level tensor calculation is unnecessary for the square: naturality of the
ordinary restriction cube and adjunction mates prove it for all derived inputs.
The bounded-flat argument is still proved separately in `extension_flat_kflat`.

The finite-coefficient realization requires an explicit constant-scalar
coordinate comparison. `lem-sf-intrinsic-realization-flat` concerns the distinct
intrinsic realization for a ring in `Type u` and modules over its `ULift`;
it does not directly have the target's `Type (u+1)` fixed-ring realization.
The new lemma supplies precisely the latter endpoints, with a concrete unit
construction. The proof is independent of a bound or a time-limit workaround.
The narrow module environment avoids coefficient-instance conflicts when its
construction is elaborated alongside all the main mate APIs.

A source-only traversal found zero current Lean importers of the item. Both DAG
attachments and their unfinished parents are retained; zero importers was not
used to prune the item. A full DAG traversal also encountered the existing
`lemma-weil-pbc-derived-exchange-replacement` /
`lem-weil-pbc-derived-exchange-termwise` /
`lem-weil-pbc-derived-exchange-bounded-comparison` cycle below the original
etale tensor dependencies. This delivery creates no edge among those nodes and
makes no unrelated repair there.

## New nodes

`lem-sp-finite-coefficient-realization-flat` states flatness of the actual
finite-coefficient realization restricted along the canonical commutative
constant-ring comparison. Its own module and full proof are included. The
sheafification unit is linear because the comparison preserves constant
sections; forgetting to additive sheaves identifies it with an invertible
sheafification unit. Constant-scalar restriction then reflects flatness.
Empty sites, the zero ring and the zero sheaf are included. Searches of
Mathlib by LeanSearch, LeanFinder, Loogle and grep, and of blueprint titles/statements,
found no theorem with these actual realization endpoints. Related constant
module and intrinsic-realization results have different domains. The new node
inherits the item's chapter, unit and blueprint ancestor. Change record:
`coord/changes/F9-open-scalar-site-proof-context.md`.

## Second reading by F9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
