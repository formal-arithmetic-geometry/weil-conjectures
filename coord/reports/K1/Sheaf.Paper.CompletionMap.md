## What changed

Proved the completion-map module using its existing strict quotient tower and explicit
shifted mapping cocone. Quotient augmentations are constructed from the scalar-extension
unit and the sheafification unit; their section formulas prove uniqueness and strict
transition compatibility. Product extensionality proves the zero-homotopy relation, and
Mathlib's lift projection formula proves the derived quotient projection equation.

A private, proved helper translates the epimorphism clause of
`ProEt.countableProducts_exact` into `CountableAB4Star`. The existing
`derivedCategory_countableProducts_core` supplies existence of the derived product and
the limiting localized product cone. Transport across `Discrete.compNatIsoDiscrete`
identifies the canonical comparison, and Mathlib's limit criterion proves it invertible.
The localized cocone triangle is transported through this comparison with the prescribed
boundary. A private, proved mapping-cocone helper constructs the strict tower map by
shifting `mappingCone.map`, and proves uniqueness by `mappingCocone.id_X`.
The triangle calculation uses explicit comparison-projection equations and functor laws
to avoid expensive simplifier unfolding of the coefficient tower.

All existing statements, definitions, public imports, universes and visibility are
preserved. Updated `def-weil-pbc-completion-map` only in `proof`, `proof_deps` and
`proof_origin` to record the realized route. No consumer adaptation is needed.
The preflight requested a conservative record for the additional opening commands:
`coord/changes/K1-completion-map-proof-scope.md`. It records the exact proof scopes
and reviews both downstream consumers, held by J3 and Y2; their public API and
existing definition bodies are unchanged.

Validation: the complete module compiled through `lcompile.py` with exit code 0 in
35.5 seconds, without errors or warnings. All 26 existing declaration signatures and
all public imports were compared with the repository version and remain identical.
The delivered source has no development profiler options, temporary checkpoints,
forbidden declarations, over-width Lean lines, or `sorry`.

## Proved and sorry left

Holes closed: 8 of 8, all attached to `def-weil-pbc-completion-map`:

- `AlgebraicGeometry.Scheme.adicReductionAugmentation_exists`.
- `AlgebraicGeometry.Scheme.adicReductionAugmentation_step`.
- `AlgebraicGeometry.Scheme.adicCompletionLift_relation`.
- `AlgebraicGeometry.Scheme.adicCompletionMap_projection`.
- `AlgebraicGeometry.Scheme.adicReductionSequence_hasProduct`.
- `AlgebraicGeometry.Scheme.adicCompletionProductComparison_isIso`.
- `AlgebraicGeometry.Scheme.adicCompletion_distinguished`.
- `AlgebraicGeometry.Scheme.adicCompletionTowerMap_exists`.

Holes added: 0. Split-offs: 0. No `sorry` remains in the delivered module.
The imported countable-exactness and derived-product theory retain their own existing
proof obligations; this delivery does not claim their transitive closure is axiom-free.

## No longer needed

Removed the proof import `Sheaf.Algebra.Homology.KFlatResolutionGeneral`: this module is
given a fixed `AdicKFlatModel` and never chooses or resolves a model. The resolution node
`lem-pc-kflat-resolution` remains a statement dependency through that model interface,
but is not needed as a direct proof dependency or import here.

Removed the retired re-export module
`Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`, replacing it with the actual
source module `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts`.
The node `lem-weil-derived-limit-products-core` remains used. No mathematical dependency
on exact countable products, derived products, or the stipulated adic limit was bypassed.
All original public imports remain necessary for the exported constructions.

No module is withdrawn. These are pruning decisions for this item's imports, not claims
that other parents no longer use the removed modules. The unit realization has no own
statement or proof step carried by this definition, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The node had no numbered proof steps (`proof: []`), although the module docstrings carried
the complete plan. The node now records the actual scalar-unit, exact-product, triangle
transport and strict-tower-map arguments. The node's recorded derived-product dependency
already points to the upstream module; the old Lean proof import still used its retired
re-export, which is unnecessary.

Mathlib search: LeanFinder for a cochain-complex map into the mapping cocone and preservation
of countable products returned localization fractions and `DerivedCategory.Q`, rather
than a whole completion-map theorem. Loogle for `"mappingCocone"` found the constructor
and projection API. The launcher grep search found `mappingCocone_triangle_distinguished`
and `Discrete.compNatIsoDiscrete`. Local searches confirmed the existing scalar-extension
unit, sheafification naturality and tower-endomorphism naturality APIs.

Edge cases are covered by the generic constructions: zero complexes, the zero ring,
unit and zero ideals, zero differentials, zero tower maps, and every integer degree.
No nonzero-coefficient, boundedness, finiteness-of-quotient or extra completeness
hypothesis was introduced. Data selected by existing definitions remain determined by
unique section or coordinate formulas; no arbitrary witness of mere existence was added.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
