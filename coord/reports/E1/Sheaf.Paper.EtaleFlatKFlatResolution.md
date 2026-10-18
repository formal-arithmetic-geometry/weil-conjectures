## What changed

Proved `AlgebraicGeometry.Scheme.exists_etale_flat_isKFlat_resolution` in
`Sheaf.Paper.EtaleFlatKFlatResolution`, with its signature, visibility, definitions,
and public imports unchanged. The proof specializes the existing
`CochainComplex.exists_isKFlatResolutionIndependentCoefficients` to the constant
coefficient sheaf on the small etale site. It retains the complex, augmentation,
K-flatness and quasi-isomorphism, and discards degreewise epimorphy.

Added one proof-only import,
`Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients`, to use the existing
`SheafOfModules.siteSheafTensorRightIso`. Exactness transfers along its inverse,
giving exactly `IsFlatOnSite` in each degree. Both proof-only imports are used.
Updated the item's node proof and proof dependencies to record this API comparison.
The existing generic tensor comparison is used as a tool from
`lem-weil-pbc-independent-sheaf-tensor-colimits`; it changes no unit-level route.
No new approval is written into `tool_uses`.

Validation: the module compiled cleanly with `lcompile.py`. The statement is unchanged
and introduces no extra hypothesis. The resolution theorem applies to arbitrary
complexes, the zero ring and the empty scheme as well as other schemes and rings.
The tensor comparison applies at the independent coefficient universe `u + 1`.
The source checked was Stacks `sites-cohomology.tex`,
`lemma-K-flat-resolution` (Tag 06YS). The unit's realized statement/steps lists are
empty, and the proof follows the already accepted ringed-site specialization plan.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.exists_etale_flat_isKFlat_resolution`
(node `lem-kun-flat-resolution-existence`).

Added 0 holes and split off 0 statements. No `sorry` remains in the delivered module.
No declaration is merely renamed or repackaged under a new holed theorem.

## No longer needed

No existing import, declared proof dependency, node or module is pruned. All existing
statement imports are preserved. The original three proof dependencies are used;
the tensor comparison and flatness-definition dependencies are now explicit.
No bounded-above replacement tower, truncation, telescope or K-injective module is
needed by this specialization. These were already absent from the accepted DAG
proof and the item's imports, so no newly pruned module is claimed.

## Where the brief, the DAG or earlier work was wrong

The planned flatness conclusion uses `IsFlatOnSite`, whereas the general resolution
API returns exactness of monoidal `tensorRight`. The existing proved
`siteSheafTensorRightIso` bridges these formulations; no definition repair is needed.

The current blueprint update describes a composite through a K-injective resolution
without providing a chain map back to the original complex. The accepted node
already records this direction error and uses Stacks 06YS directly. This delivery
keeps that accepted correction and the statement unchanged.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
