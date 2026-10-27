## What changed

Filled `CategoryTheory.Over.DescentDatum.isEffective_of_isQuasiAffineHom_fpqc` in
`Sheaf.AlgebraicGeometry.QuasiAffineFpqcDescent` from the existing stronger theorem
`CategoryTheory.Over.DescentDatum.isEffective_of_indQuasiAffine_fpqc` (Stacks 0APK).
For every affine target open U, identify the pullback with the preimage open in V.
Each compact open K of this quasi-affine scheme is quasi-affine, and its structure
map to affine U is quasi-compact, hence quasi-affine. This supplies precisely the
stronger theorem's chart hypothesis. No signature, definition, or public import changes.
The original docstring retains the previous Stacks 0247 proof plan; the DAG now
records the shorter proof actually used.

Single-file compilation passed in 6.0 seconds with no errors or warnings.
Both Lean import reachability and the DAG were checked for cycles; neither has a
path from the stronger theorem back to this item. The unit's realized statement
and proof-step lists are empty, and this change leaves the unit route untouched.
The stronger theorem is general fpqc scheme descent, not trace-formula machinery.
Edge cases: empty K has compact empty scheme and the same immersion argument;
empty V makes every K empty; identity covers and non-affine bases use exactly the
same affine-open chart argument. No flatness of the open cover or presentation
assumption on V is introduced.

## Proved and sorry left

Closed 1 of 1 existing holes:
`CategoryTheory.Over.DescentDatum.isEffective_of_isQuasiAffineHom_fpqc`
(node `lem-trf-quasi-affine-fpqc-effective-descent`).
Remaining holes in the delivered module: none. Added holes: zero. Split off: zero.
This is a complete proof from an existing stated dependency, not a claim that the
transitive dependency tree is axiom-free: the imported
`isEffective_of_indQuasiAffine_fpqc` still has its existing sorry, not added or
changed by this delivery.

## No longer needed

Removed private proof imports:
- `Mathlib.AlgebraicGeometry.Limits`
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`
- `Mathlib.AlgebraicGeometry.PullbackCarrier`
- `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`
- `Mathlib.RingTheory.Spectrum.Prime.Topology`
- `WeilConjectures.AlgebraicGeometry.AffineFpqcDescent`
- `WeilConjectures.AlgebraicGeometry.FpqcDescendingTypesMorphisms`
- `Sheaf.AlgebraicGeometry.QuasiAffineBaseChange`

The following former direct proof dependencies are no longer needed by this
module, because the general ind-quasi-affine descent theorem supplies effectivity:

- `lem-trf-quasi-affine-base-change`
- `lem-weil-pbc-scheme-coproduct-family`
- `lem-weil-pbc-spec-clopen-idempotent`
- `lem-weil-pbc-principal-localization-open-immersion`
- `lem-weil-pbc-affine-morphism-permanence`
- `def-weil-affine-spectrum`
- `lem-weil-pbc-affine-scheme-qcqs`
- `def-weil-pbc-fpqc-covering`
- `lem-trf-canonical-affine-envelope-descent-datum`
- `lem-galois-fpqc-affine-descent-effective`
- `lem-weil-pbc-flat-morphism-base-change`
- `lem-weil-pbc-surjective-base-change`
- `lem-weil-pbc-open-immersion-base-change`
- `lem-trf-invariant-open-image-pullback`
- `lem-galois-fpqc-descending-types-morphisms`

The two obsolete top-level tool approvals
`lem-galois-fpqc-affine-descent-effective` and
`lem-galois-fpqc-descending-types-morphisms` are removed from this node. Their
existing approvals elsewhere are unaffected. These tools and some other listed
nodes remain transitive dependencies of the stronger theorem; this report does
not assert that they disappear from the targets' full closure. In particular,
`CanonicalAffineEnvelopeDescentDatum` and `InvariantOpenImagePullback` are no
longer direct prerequisites here; no source-library declaration is withdrawn.
No module is deleted. The remaining private Mathlib import
`Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` supplies the quasi-compactness
instance used for K → U. The stronger descent theorem is the only added import.

## Where the brief, the DAG or earlier work was wrong

The original plan separately descends a canonical affine envelope and an invariant
open, but the already stated ind-quasi-affine descent theorem subsumes its
conclusion. The node's independent DAG reviewer explicitly noted this overlap
on 2026-10-22. The chart implication is proved directly using existing Mathlib
and source-library declarations, avoiding any new statement or hole. No false
statement or broken tool was found. No change record is needed: only a theorem
proof, private proof imports, and allowed node proof fields changed.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
