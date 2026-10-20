## What changed

Replaced the `sorry` in `AlgebraicGeometry.Etale.existsUnique_vectorIntegrationGluing`
by a complete combination of concentration, uniquely normalized degree-zero
identification, the local derived-to-sheaf Hom correspondence, and étale-family
sheaf-Hom gluing. An extra-frame restriction lemma extends the chosen matching
family by any requested frame; uniqueness on the original cover gives the universal
normalization, including every normalized projective-line datum family.

The existing coefficient, geometry, chart, local-trace and normalization block moves
verbatim to `Sheaf.AlgebraicGeometry.VectorBundleIntegrationCharts`, publicly re-exported
by the item. This avoids the import cycle between the local overlap statement and
the global gluing proof. Original signatures and defining data are preserved. See
`coord/changes/F1-vector-integration-charts.md`.

Consumer checks against the overlay confirm that VectorIntegrationMate,
VectorPurityNormalization, VectorPurityBaseChange, Targets.VectorBundlePurity
and AmbientDiagonalPurityBaseChange compile unchanged. The change record lists
all 87 current transitive importers. The unclaimed
VectorPurityDirectSum exceeded 60 seconds both with the overlay and against the
published baseline. A local singleFunctor folding annotation and transparency options
make it compile in 30.3 seconds while retaining every declaration and data body verbatim.
The annotation is not exported. The unchanged additional consumer FiniteRingSectionDeformation exceeds 60 seconds
with the overlay. Its published-baseline profiled run finishes in 57.3 seconds,
including 35.8 seconds waiting for asynchronous declaration checks at end of input;
a second baseline profiling run also exceeds 60 seconds. No successful overlay
check is claimed for that consumer. Broad folding settings produce existing
definitional-comparison errors and narrower settings do not improve its timing;
all diagnostic changes to that consumer were discarded. See `coord/changes/F1-vector-direct-sum-folding.md`;
no other consumer adaptation is included. The final item check takes 21.2 seconds.

Independent proved results supply concentration, normalized derived identifications,
cover-family gluing, local Hom transport, uniqueness of normalized Tate transport,
injectivity of the constant-coefficient derived class realization, and uniqueness
of projective-line data. The latter proves base change for every normalized family
from the existing projective-line adjunction theorem. The remaining geometric
result is the fixed-family local overlap equality with base-change equations.

## Proved and sorry left

Original holes: one, `AlgebraicGeometry.Etale.existsUnique_vectorIntegrationGluing`.
Its body is complete from the separate overlap result. This is a decomposition:
one upper hole closed, one strictly local lower hole added, zero net holes closed.

The only added hole is
`AlgebraicGeometry.Etale.vectorIntegrationLocalSheafTrace_compatible_of_baseChange`
(node `lem-amb-vector-integration-local-trace-compatibility`). It asserts equality
of local descent components for two frames, a fixed normalized family and its
base-change equations. Its conclusion has no global existence, concentration,
normalized identification or uniqueness. The docstring gives the complete geometric
argument, including restriction, inverse-transpose coordinates, exchange pasting,
Tate comparisons and linear trace invariance. Its proof is exactly `by sorry`.

The individual axiom probe for `ordinaryFiniteClass_injective` reports exactly
`propext`, `Classical.choice` and `Quot.sound`. The first delivery preflight
accepted the source checks, but its automated direct-sum axiom probe timed out;
the merge check reruns that probe.

Every other added theorem is proved. In particular:

- `vectorIntegration_cohomology_zero`.
- `DerivedCategory.existsUnique_iso_single_homology_zero` and
  `DerivedCategory.existsUnique_normalized_iso_and_map`.
- `existsUnique_etaleSheafHom_of_family` and
  `etaleSheafHom_restriction_eq_of_compatible`, and `descentComponent_eq_of_mono`.
- `CategoryTheory.fullyFaithfulHomEquivOfIsos`, its `_symm_apply` equation,
  `CategoryTheory.fullyFaithfulHomEquivOfCompIso`, its `_map` equation, and
  `CategoryTheory.homEquiv_comp_iso_eq_iff`.
- `DerivedCategory.fullyFaithfulSingleFunctor`, `etaleSingleRestrictionIso`,
  `etaleDegreeZeroHomEquiv`, `etaleDegreeZeroHomEquiv_map`, and
  `etaleDegreeZeroHomEquiv_unit_normalization`.
- `ordinaryFiniteTwistTransport_unique`, `ordinaryFiniteClass_injective`,
  `ordinaryFiniteP1Datum_unique`, and `ordinaryFiniteP1BaseChange_of_normalization`.
- `vectorIntegrationLocalSheafTrace_normalization_iff` and
  `vectorIntegrationLocalSheafTrace_compatible`, the latter reducing arbitrary
  normalized families to the fixed-family overlap lemma.
- Both private normalization/gluing helpers in the item.

No definition contains a hole or an arbitrary witness of mere existence. Canonical
Hom preimages are determined by full faithfulness; the original global definition
still uses the uniquely characterized gluing theorem. No existing proved theorem
is replaced by `sorry`. Existing imported holes are unchanged.

## No longer needed

The following three modules leave this item's import closure:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.HomCoverGluing`: retired empty module;
  the new proved theorem glues constant-coefficient ModuleCat sheaves directly.
- `Sheaf.AlgebraicGeometry.IsIsoIffOfJointlySurjectiveEtaleFamily`: its interface
  is for abelian sheaves; concentration uses the proved source ModuleCat API.
- `Sheaf.CategoryTheory.TruncationDescends`: replaced by Mathlib's standard
  t-structure and the proved normalized degree-zero identification.

The declarations attached to `lem-pur-sheaf-hom-cover-gluing`,
`lem-weil-pbc-etale-cover-detects-iso`, `lem-weil-pbc-truncation-descends`, and
`lem-weil-pbc-truncation-cohomology` are not used by this proof. The source
ModuleCat conservativity API and Mathlib heart APIs supply their needed roles. No module is withdrawn, and no source-library declaration is changed.
These are item-closure observations, not claims of removal from every target's
closure. The blueprint unit's affine trace, coordinate-transition, linear-invariance,
local-overlap and gluing route is retained. The original node's statement-dependency list is retained; the new construction
node is reached through the actual proof dependencies, which describe the new route. No unit record or target statement changes.

## Where the brief, the DAG or earlier work was wrong

The original definition node has no top-level proof steps, but its expanded
statement, theorem docstring and current blueprint provide the concentration,
overlap and gluing argument. The updated proof field records that implementation.

The old sheaf-Hom node's attached result concerns `SheafOfModules`; this item uses
`Sheaf ... (ModuleCat A)`. The new covering-family theorem uses the actual source
`EtaleMorphismDescent` and sheaf-of-Hom APIs, without identifying these representations.

The separate remaining calculation concerns the actual chart exchange and coefficient
composites under restriction of a frame and coordinate change. Linear trace invariance
applies after those composites have been identified with the affine linear action;
it does not itself state that identification for `vectorIntegrationChart`. No existing
library declaration states this overlap identification. The new hole isolates exactly
that local calculation, rather than renaming the global gluing theorem.

Universal normalization permits every normalized datum family, not just one with
base change supplied as an extra hypothesis. The proved uniqueness results establish
base change from normalization, so the original conclusion and quantification are
preserved; the fixed-family hypothesis occurs only in the separate local lemma.

## New nodes

- `def-amb-vector-integration-charts`: unchanged relocated constructions.
- `lem-amb-vector-integration-cohomology-zero`: vanishing outside degree zero.
- `lem-amb-derived-degree-zero-normalization`: normalized heart identification and
  combination with a uniquely characterized sheaf map.
- `lem-amb-etale-sheaf-hom-family-gluing`: gluing and the extra-frame restriction API.
- `lem-amb-etale-degree-zero-hom`: categorical transport and local normalization.
- `lem-amb-ordinary-finite-twist-transport-uniqueness`: roots and line normalization.
- `lem-amb-ordinary-finite-class-injectivity`: constant-generator corepresentation
  and the proved source Ext-to-cohomology comparison.
- `lem-amb-ordinary-finite-p1-datum-uniqueness`: Chern/decomposition/counit uniqueness
  and the base-change corollary.
- `lem-amb-vector-integration-local-trace-compatibility`: the strict local overlap
  statement, local sheaf-trace construction and proved arbitrary-family wrapper.

## Forced adaptations

`Sheaf.Paper.VectorPurityDirectSum` is unclaimed. Its original compiler result is
`timeout after 60 s`, both against the changed dependencies and against the
published baseline. The added lines are two transparency-respecting unification
options and a local irreducibility attribute for `DerivedCategory.singleFunctors`.
They prevent repeated unfolding during the unchanged tensor-unit comparisons;
the adapted module compiles in 30.3 seconds. Every declaration, signature, public
attribute and data body is byte-identical. The exact old and new prefix, including
`purityPowerAdd`, is in `coord/changes/F1-vector-direct-sum-folding.md`.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
