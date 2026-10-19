## What changed

Proved `AlgebraicGeometry.isZero_higherDirectImage_open_of_stalk_dimension_le_one`
in `Sheaf.AlgebraicGeometry.OpenDimOneHigherDirectImageVanishing` without changing
its signature or any definition. The proof follows Stacks Varieties, Tag 09N8
(`literature/stacks-project/varieties.tex`, lemma-affine, lines 7747–7779):
retrocompactness gives quasi-compactness, the local-spectrum classification makes
the pulled-back open affine, affine vanishing annihilates its higher direct image,
and flat base change plus the local adjoint stalk comparison gives zero stalks.
The tensor pullback is compared with the usual pullback by uniqueness of left
adjoints to obtain quasi-coherence. The argument includes the empty open and the
whole local spectrum, and uses the stated hypothesis `0 < p` only for affine vanishing.

Added proof-only imports of `SpecLocalRingCanonicalMorphism`,
`FlatBaseChangeMapSectionsLift`, `FlatBaseChangeResolutionIso`,
`LocalPullbackAdjointStalkIso` (all under `Sheaf.AlgebraicGeometry`) and
`Mathlib.Topology.Sheaves.Abelian`. Updated the existing item's DAG proof and
dependencies to these actual declarations. No public import or interface changed.
The item compiles cleanly with lcompile.py (11.5 seconds).

The following existing nodes are used as generic tools from another unit:
`lem-weil-pbc-spec-local-ring-canonical-morphism`,
`lem-weil-pbc-flat-base-change-lift`,
`lem-weil-pbc-flat-base-change-resolution-iso`, and
`lem-weil-pbc-local-pullback-adjoint-stalk-iso`.
They supply the canonical local flat morphism, actual sheaf-valued flat base-change
map and its stalk detection; none replaces an endpoints-unit argument. The unit's
route and its statement are unchanged. Maintainer tool-use approvals, if required,
are left to the independent review; no new approval is inserted by this delivery.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.isZero_higherDirectImage_open_of_stalk_dimension_le_one`
(node `lem-a1-open-dimension-one-higher-image-vanishing`).

The item originally had one sorry and now has zero. Added zero holes; split off
zero statements. The existing imported theorem
`AlgebraicGeometry.localSpectrum_open_classification` remains an existing
proof dependency, not a new hole or a claim of a completed transitive proof.

## No longer needed

Removed proof imports:
- `Mathlib.RingTheory.Flat.Localization`: canonical-local-morphism flatness is
  already provided by `Scheme.fromSpecStalk_local_properties`.
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`: its field-extension
  cohomology dimension theorem does not provide the sheaf-valued map needed here.
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism`:
  the used affine vanishing theorem is imported from its implementation module
  `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing`,
  which was already imported by the item.

Removed direct proof-dependency edges to
`lem-weil-pbc-affine-open-stalk-localization` and
`lem-weil-pbc-localization-flat`: their local calculations are encapsulated in
`lem-weil-pbc-spec-local-ring-canonical-morphism` and are not repeated here.
Removed the edge and obsolete top-level tool-use entry for
`lem-pc-flat-base-change-cohom`, replacing its unusable Lean attachment with
`lem-weil-pbc-flat-base-change-resolution-iso` and its comparison-lift API.
General flat base change remains essential mathematically. No claim is made that
these nodes are globally unreachable: other modules and the canonical morphism's
own dependencies may still need them. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node `lem-pc-flat-base-change-cohom` records
`AlgebraicGeometry.Scheme.Modules.finrankH_pullback` in `EulerChar`. Its signature
only compares cohomology dimensions under a field extension, whereas this proof
needs a sheaf-valued comparison over an arbitrary local ring. The existing
`flatBaseChangeResolutionBeta_isIso` has precisely the required generality.
No dependency statement or definition is changed.

The node for `lem-pc-affine-morphism-hi` names the re-exporting module
`DirectImage.AffineMorphism`; the declaration itself lives in `AffineVanishing`.
The proof uses the latter directly without changing that node's attachment.

The retained draft had not been compiled because earlier server requests received
no answer. In this session the server responded; the sole Lean error was a set
coercion in the compactness argument, repaired by exposing the set preimage.
Removed all letI/haveI style warnings. No new nodes or change records are needed.

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
