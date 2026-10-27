## What changed

Constructed the canonical root-limit adjunct from the cone of finite-root maps. Built the
ordinary tensor adjuncts and finite-coefficient reduction using scalar-extension lifts.
Identity and composition are checked using the actual fibre-product comparisons, and the
reduction square is checked on original pure sections. All helpers are private.

Replaced the expensive concrete coherence record by `AmbRootTowerPullbackCoherenceData`,
parameterized by its two module families and pure-section functions. The original
`AmbRootTowerPullbackCoherence` is its specialization to the unchanged concrete constructions.
All 20 field types specialize to the original equations. Each law is a named proposition,
kept abstract during record generation. Four proved canonical-instance facts cache
sheafification and the root-tower limit. Disabled unused generated constructor-index,
SizeOf and injectivity declarations. The current direct importer, `Sheaf.Paper.AmbTateRootProjectionReduction`, uses field
notation; no downstream module uses the old projection namespace.
Change record: `coord/changes/amb-root-coherence-generation.md`.

Repair of returned head `1b22ee7668d` (2026-10-24): the earlier reviewer accepted the proof,
but its landing failed while applying a change-record fix. The record remains at
`coord/changes/amb-root-coherence-generation.md` in this delivery. Corrected its field count
from 21 to 20 and replaced the stale assertion of no downstream users with the current
consumer list. The landing tool names an override for this record
`amb-root-coherence-generation.change.md`; the failed override used the `.md` basename.
The delivery command rebuilds the retained packet on the current `sheaf-dag` base.

Updated the node proof to this direct-image adjunct argument. The construction does not require
inverse image to preserve the infinite root limit.

## Proved and sorry left

The delivery closes the original single hole:
`AlgebraicGeometry.Scheme.ambRootTowerPullbackCoherence` (1 of 1).
No holes are added or split off. The item contains zero remaining `sorry` declarations.
The repaired packet compiled cleanly on 2026-10-24 through `lcompile.py`: the complete
item took 55.2 seconds, and its unchanged direct consumer
`Sheaf.Paper.AmbTateRootProjectionReduction` took 95.9 seconds (both exit code 0).
The consumer was copied only for this compatibility check and removed from the packet
afterwards; it is not adapted or delivered. No proof is split off.

## No longer needed

The direct adjunct construction avoids these planned proof dependencies:

- `lem-weil-pbc-left-exact-site-inverse-image-tensor`
  (`Sheaf.CategoryTheory.SiteInverseImageTensor`): the constant comparison follows from the
  constant sheaf adjunction and preservation of a terminal object.
- `lem-pe-constant-left-module-inverse-image`
  (`Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`): the actual constant map is identified
  directly through its adjunct.
- `lem-trf-site-inverse-image-composition-generators`
  (`Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators`): finite roots are compared as
  units under the specified fibre-product projection.
- `lem-pur-independent-inverse-image-tensor-comparison`
  (`Sheaf.SecSmoothPurity.CochainInverseComparison`): the statement already asks for adjuncts,
  which are built directly by scalar extension.
- `lem-pur-inverse-image-tensor-adjoint-test`
  (`Sheaf.AlgebraicGeometry.ProEtaleTensorAdjointTest`): ordinary sheafification and tensor
  generation detect equality of the displayed adjuncts.

Removed the redundant public import
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`.
Removed those five unused entries from the node’s top-level `tool_uses`, preserving the
remaining approval for `lem-pur-roots-of-unity-inverse-image-iso`.
These dependencies may still have other consumers; this delivery does not withdraw them.

## Where the brief, the DAG or earlier work was wrong

The planned inverse-image tensor and generator infrastructure is unnecessary for the displayed
adjunct formulation. No mathematical statement is changed.

The original change record's claim that no downstream module uses the record is now stale:
`Sheaf.Paper.AmbTateRootProjectionReduction` imports it and uses its fields. The repaired
change record lists that consumer and the two transitive importers. The earlier landing
failure concerned the reviewer override basename, not the Lean proof or a missing sandbox
change record.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
