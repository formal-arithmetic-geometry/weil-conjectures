## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.CondensedRing.common_field_lattice_generators`
by an explicit common-field construction and a proof assembling the per-generator properties.
The finite field comes from `PadicAlgCl.finiteSubextensions_directed`; both inclusions are
proved by cases on `Fin 2`. The scalar maps compose definitionally to the original map, so the general tower theorem
specializes without an equality-transport morphism.

Proved private helpers identifying scalar extension of the regular module with the regular
target module, preserving finite-free presentations, and preserving lisseness on the original
trivializing cover via `pullIso`. No flatness assumption on the coefficient map is used.

Added `ScalarSixLisseExtensionConstructible`, whose theorem is completely proved from the
separate module-heart constructibility assertion. Its proof composes the three exact-functor
single-complex comparisons, proves boundedness in [0,0], transports degree-zero constructibility,
and handles every other cohomology module by a rank-zero presentation.

Added two genuinely separate results from the source argument: constructibility of a normalized
integral module extension, and the normalized coefficient-tower comparison for one lisse
generator. They have their own modules, source proofs in their docstrings, and DAG nodes.
Updated the item's proof route and added nodes for these interfaces and the proved degree-zero
reduction. Existing statements and definitions, including the target theorem's signature, are
unchanged. No source-library file was changed.

## Proved and sorry left

Original item: one hole closed, in
`AlgebraicGeometry.ProEtale.CondensedRing.common_field_lattice_generators`; zero holes remain
in the item module. This is a decomposition, not a net proof of the original mathematics:
two holes are added in separate source results.

The new theorem
`AlgebraicGeometry.ProEtale.CondensedRing.normalized_integral_extension_constructible`
is proved, with no hole in its body, from the heart-level assertion.

Every retained hole:

- `AlgebraicGeometry.ProEtale.CondensedRing.normalized_integral_heart_extension_constructible`,
  in `Sheaf.SixFunctors.ScalarSixHeartLatticeExtension`, node
  `lem-sfb-normalized-integral-heart-extension-constructible`.
- `AlgebraicGeometry.ProEtale.CondensedRing.lisse_generator_normalized_tower`,
  in `Sheaf.SixFunctors.ScalarSixLisseTowerComparison`, node
  `lem-sfb-lisse-generator-normalized-tower`.

The first is only the geometric constructibility assertion in the abelian module heart;
it has no common-field choice, scalar-extension map, derived boundedness, or tower comparison.
The second concerns one lisse module and a general coefficient tower; it has neither the
common-field choice nor any bounded-constructibility assertion. The final Lean proof combines
them with the independently proved finite-field and finite-free calculations.

## No longer needed

Removed the item's direct proof import of `Sheaf.Algebra.Homology.LocallyFreeDerivedScalars`.
It remains needed in the scalar-tower node's proof plan. Retained the direct import of
`Sheaf.SixFunctors.IntegralModelsGenerators`, which realizes a step of the unit's route
and remains needed by the module-heart node's proof plan. Ordinary preservation of
lisseness uses a direct finite-biproduct argument rather than the sectionwise derived-scalar
interface. No existing module is withdrawn; no unit statement or proof step is bypassed.
No whole module is pruned from the DAG by this delivery.

## Where the brief, the DAG or earlier work was wrong

The plan's mathematical route is sound, but the recorded Lean declarations do not provide
all the presentation bridges as direct applications. `integral_models_generators` clause (3)
uses closed pushforward after the actual open extension and the finite-constant-model
predicate. The item instead uses an arbitrary normalized coherent extension, transported
through the internal/sectionwise module equivalence, and locally finite presentations.
The heart-level node isolates exactly this bridge; finite constant models already contain
finite presentations, so that direction does not need a new coefficient-normalization result.

Likewise, `scalarSixPullback` asserts existence of particular coherent witnesses. The item
accepts arbitrary normalized H, D, G and C. Its normalization equation therefore requires
transport through uniqueness of the normalized open and closed comparisons, not merely
projection of the existential theorem. The tower node records that compatibility explicitly,
together with the canonical derived-counit degree-zero comparison for a lisse module.
These are missing interface proofs, not assertions that a dependency's `sorry` is an obstacle.

## New nodes

`lem-sfb-normalized-integral-heart-extension-constructible`:
`Sheaf.SixFunctors.ScalarSixHeartLatticeExtension`, the geometric module-heart part of
source step 4. Its proof plan uses the existing integral-generators and normalized-extension
coherence declarations.

`lem-sfb-normalized-integral-extension-constructible`:
`Sheaf.SixFunctors.ScalarSixLisseExtensionConstructible`, a proved reduction from the preceding
module-heart result to bounded constructibility using exact functor/single-complex comparisons.

`lem-sfb-lisse-generator-normalized-tower`:
`Sheaf.SixFunctors.ScalarSixLisseTowerComparison`, the single-generator scalar-tower calculation
from source steps 3 and 5, with its full restriction normalization stated explicitly.

No statement or definition change records are needed.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
