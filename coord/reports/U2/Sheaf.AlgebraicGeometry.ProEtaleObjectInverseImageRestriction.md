## What changed

Completed the full proof of `AlgebraicGeometry.Scheme.proEtaleObjectInverseImageRestriction`
with its original signature. Retained and checked the earlier index, presheaf, sheaf and
coefficient-map arguments. Finished the module clause using the existing tensor-normalized
`proEtaleRingModuleAdjunction` and Mathlib's `SheafOfModules.pushforwardPushforwardAdj`.
The two coefficient compatibility equations follow from sheafification uniqueness on
constant sections. Uniqueness of left adjoints gives the module isomorphism and its
naturality. The required coefficient-map invertibility is proved locally from the
already established comparison equation.

All added helpers are private and fully proved. The four original public imports,
all existing public declarations and all target statements are unchanged. The parent
node records this shorter route. The retained new module and node were never delivered;
their outstanding obligation is now proved privately in the item module, so they are
omitted from this delivery. The declaration-scoped proof options are documented in
`coord/changes/U2-proetale-object-restriction-proof-options.md`, as required by
the static preflight; no public interface or consumer changes.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.Scheme.proEtaleObjectInverseImageRestriction`.
No `sorry` remains in the delivered module. Zero holes added; zero split-offs delivered.
Private helpers prove the distinguished-coprojection formula, the sheaf condition,
constant-section normalization, the specified coefficient-map identity, the coefficient
unit and counit equations, and the natural module pullback comparison.

## No longer needed

Removed the original proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage` (already available through statement imports).

Added the proof-only import
`Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction`.
The retained split module `Sheaf.AlgebraicGeometry.ProEtaleObjectModulePullbackRestriction`
is unnecessary and is not delivered; its unlanded node is not delivered either.

The parent no longer directly uses `def-pc-fibre-product`,
`def-pur-localized-ringed-site`,
`def-pur-sheaf-tensor-product`, or `def-weil-presheaf-modules-sheafification`.
Mathlib's site adjunction and sheafification APIs handle the first comparisons; the
existing normalized module adjunction handles the tensor construction. Tensor and
module-sheafification theory remains a transitive dependency of that adjunction, so
this report does not claim those modules are globally pruned. The continuous-functor
sheaf adjunction remains a direct dependency: its unit formula is used to identify
the specified coefficient map. The unit's lattice,
torsion and Milnor steps are preserved.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the module compatibility and scalar-extension collapse as a
new hole. Those calculations are already represented by the existing normalized module
adjunction. Once its right adjoint is identified with the right adjoint of sectionwise
restriction, uniqueness of left adjoints completes the argument. No mathematical
statement error or excluded edge case was found: the proof works for the identity,
nonmonomorphic site objects, and the zero coefficient ring. No finiteness hypothesis
is added.

Validation: the completed module is checked with lcompile.py and the required delivery
preflight, including its axiom probe. Delivery output records the final check results.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
