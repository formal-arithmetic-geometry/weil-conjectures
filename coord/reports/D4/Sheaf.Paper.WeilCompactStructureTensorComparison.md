## What changed

Proved `AlgebraicGeometry.WeilComplex.native_compact_structure_tensor_comparison`
in `Sheaf.Paper.WeilCompactStructureTensorComparison`, with its statement and all
existing definitions unchanged. Destructure the normalized comparison supplied by
`native_compact_projection_formula`; specialize
`nonempty_derivedLowerShriek_comp_iso` to the structure morphism and transport its
source by `comp_over`. The displayed comparison formula is definitional. The two
Hom formulas follow by removing the identity in `Iso.homCongr`, and the two
contravariant squares follow from naturality of the inverse and forward natural
transformations, respectively, followed by associativity.

The original declaration exceeded Lean's default 200000-heartbeat elaboration
budget. A theorem-scoped `maxHeartbeats 800000` permits its existing large type
and proof to elaborate; the 60-second file limit is unchanged. No new theorem,
definition, axiom, node or source-library change is introduced.

Library search used `msearch.py` with LeanFinder (naturality of the Hom bijection
induced by an inverse natural isomorphism), Loogle (`CategoryTheory.Iso.homCongr`),
and grep (`homCongr|naturality_assoc`), together with ripgrep over both library
roots. Mathlib's existing Hom congruence and natural-transformation naturality
provide all categorical glue; the existing projection and compact-composition
declarations provide all substantive inputs. The recorded DAG route is retained. The single-file compile passed in 16.9 seconds;
the delivery checks verify the final comment-only lint fix and axiom probe.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.WeilComplex.native_compact_structure_tensor_comparison`
(node `lem-sf-weil-compact-structure-tensor-comparison`).

No `sorry` remains in the delivered module; no holes or split statements were
added. The existing imported projection-formula and compact-composition theorems
remain independent proof dependencies, as prescribed by the stage-3 brief.

## No longer needed

Removed these redundant private imports:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Sheaf.WeilSheaf.NativePullbackStarPreservation`
- `Sheaf.Paper.NativeDerivedWeilTensorConstructible`

Their required declarations and instances are already available through the
existing public imports. No DAG dependency or module is claimed pruned from the
target closure: tensor and operation preservation are encoded by the existing
restricted functors, and their dependencies remain necessary there. No public
import was changed.

## Where the brief, the DAG or earlier work was wrong

No statement or dependency mismatch was found. The DAG's geometric-domain step
is already encoded by the available instances and restricted functors; no new
Noetherianity argument is needed in this assembly proof. The comparison, inverse
Hom formula and both naturality directions agree with the recorded source and
apply without excluding identity morphisms, empty schemes, or zero inputs.

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
