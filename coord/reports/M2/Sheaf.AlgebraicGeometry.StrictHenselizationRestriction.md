## What changed

Retired the sorry-free Sheaf.AlgebraicGeometry.StrictHenselizationRestriction twin.
The canonical node now uses the unchanged source module
WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction. All seven direct live
SHEAF importers are adapted, together with the small-model consumers of its definitions.
The change record also audits the five unchanged downstream users of the adapted source
isomorphism, target isomorphism and complex section restriction.

Added three fully implemented general/bridge modules:

- PointedEtaleSectionCone: restriction from any compatible section family over an initial
  diagram of pointed etale neighbourhoods, and existence/uniqueness by the stalk colimit.
- StrictLocalSectionCone: the actual small-colimit scheme's geometric sections and their
  naturality, giving input to the general construction.
- ExactGlobalSectionsLeray: the canonical homology/Leray composite for any scheme base
  whose global sections are exact.

Exactness reuses the existing
strictHenselizationScheme_globalSections_preservesFiniteColimits instance. No upstream
source file is edited. The small scheme, structural map, and canonical restriction formulas
in every adapted consumer are preserved. The temporary comparison probe compiled successfully and checks definitional
agreement of section restrictions and the germ predicate, uniqueness-based equality of the
chosen stalk maps, and definitional agreement of Leray composites.

Validation: all 18 delivered modules compile together after import cleanup; the temporary
comparison probe also compiled and was removed. No retired-module import remains in the
combined source/sandbox graph.

Change record: coord/changes/M2-strict-henselization-restriction-generic-cone.md.

## Proved and sorry left

This is a retirement repair with zero original holes. Holes closed: none (0 of 0).
Holes added or split off: none. No sorry remains in any delivered Lean module.

The new general theorem PointedEtaleSectionCone.existsUnique_restriction is completely
proved from Mathlib's geometric-stalk colimit and final-functor colimit transfer. The
compatibility proof stored in strictLocalSectionCone is complete. All definitions contain
concrete data. The original two sorry-free specialized proofs are replaced by this general
descent and by the existing small-model exactness instance, respectively.

## No longer needed

Withdraw lean/Sheaf/AlgebraicGeometry/StrictHenselizationRestriction.lean and remove every
live import of it. Its specialized strictHenselizationCohomologyComparison has no remaining
small-model consumer and is not recreated. All seven adopted-source declarations remain
verbatim in WeilConjectures/AlgebraicGeometry/StrictHenselizationRestriction.lean.

The retired module's proof-only import Sheaf.Paper.StrictHenselizationFunctoriality and its
separate exactness argument are no longer needed for restriction construction. Other live
users still need that functoriality module; no global pruning of it is claimed. The
StrictHenselizationStructuralMap and strict-limit nodes remain necessary for the geometric
cone. The unit route through strict-local restriction and exact sections is unchanged.

The geometric cone does not import derived comparisons or exactness: those dependencies
are imported explicitly only by their consumers. Explicit proof imports of changed
transitive dependencies ensure each consumer compiles against this packet’s definitions.

Consumer proof routes replace the specialized restriction dependency by the general cone,
its small-model geometric instance, the existing small-model exactness theorem, and the
general Leray comparison as actually used. The canonical restriction node itself remains
needed and is attached to the adopted source.

## Where the brief, the DAG or earlier work was wrong

The item has no sorry: the current queue classifies it as retire. The old seven-declaration
SHEAF interface and its upstream twin use different Lean scheme models, so a direct import
replacement is invalid. The prior returned compatibility copy did not solve that problem.
This packet shares a general construction instead and retains only genuinely model-specific
geometric data; it does not create another renamed copy of the upstream restriction API.
The exactness theorem required by the small model already exists, so its proof is reused.

## New nodes

- def-weil-pbc-pointed-etale-section-cone records the general compatible-section structure,
  its component restriction, the germ-equation predicate, and the completely proved unique
  descent map. Edge cases require no locality or torsion assumption; uniqueness follows
  from initiality even when the target scheme has no points.
- def-weil-pbc-small-strict-local-section-cone records only the geometric cone data and
  its compatibility for the actual small coordinate-ring-colimit scheme.
- def-weil-pbc-exact-global-sections-leray records the canonical comparison over an arbitrary
  base with exact global sections, for every integer degree and every bounded-below complex.

Each node has its source, full construction/proof in words, search record and Lean attachment.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
