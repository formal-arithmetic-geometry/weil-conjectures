## What changed

Completed `WeilConjectures.integralCompactSupport_prescribedReductions` without changing
its signature, any public import, or any existing definition. Retained the earlier
sandbox proof and checked it against the current source. Added three proved private
helpers for intrinsic Tor invariance, transport of compact support through the canonical
realization equivalence, and compactification independence on bounded constructible
finite coefficients.

The shorter route uses `sfIntegralCompactSupport_constructible` for integral membership
and `sfCompactSupportChosenReduction_isIso` for the chosen limit. A morphism of the
specified distinguished triangles transports the latter to the supplied M and p, with
v followed by q equal to p. The dimension-bound argument follows the source's dense
compactification, exact open extension, and finite direct-image route. Successive
compatibility is proved directly by applying the adjunction to the projection equation
obtained from p followed by (1 - shift) equal to zero.

Updated the existing DAG node's proof, proof dependencies, proof origin, and removed
obsolete tool approvals. No new node or change to a public interface is needed. The theorem
docstring, node and this report record the implemented shorter proof.

Validation: a fresh full compile against the published server library passed in
37.0 seconds with exit code 0 and no warnings. Removed the retained diagnostic profiling
options before this check. Compared the theorem signature, public imports, and all three
existing instance/definition bodies with current sources: each is unchanged. The module
has no lines over 100 characters and zero `sorry` tokens. The resumed dry run compiled
and passed the axiom probe, then reported file-wide elaboration options as an interface
change. Scoped those options to the three declarations that use them. Restored three
proof-only imports identified by the gate as unit-route modules; the next validation
passed this repaired packet: dry-run commit `99c7946cb6` compiled and passed all
preflight checks, classified CODEX solely because a node file changes. No new holes
or split statements were added.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.integralCompactSupport_prescribedReductions`
(node `lem-coef-integral-compact-support`). Added zero holes; split off zero statements.
The delivered module has zero `sorry`. The three private helpers are fully proved.
The imported named results retain their own existing proof obligations; this delivery
proves the item from those declarations, as required by stage 3.

## No longer needed

Removed proof-only imports (23):

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.Immersion`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.Paper.SfIntegralReductionTower`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SfCompactSupportRestrictionOfScalars`
- `Sheaf.Paper.NormalizedDVRTower`
- `Mathlib.Algebra.Homology.DerivedCategory.Fractions`
- `Sheaf.Paper.NormalizedDVREffectivity`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Paper.EtaleCompactSupportCoefficientChange`
- `Sheaf.Paper.QcqsCompactSupportRealization`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.SecSmoothPurity.IntrinsicCompactSupportRestriction`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The following old direct proof dependencies are unnecessary in this module's proof
(their modules may remain needed elsewhere or inside the reused results):

- `lem-pc-kflat-resolution`
- `def-weil-integral-derived-reduction`
- `lem-pur-derived-change-of-rings`
- `def-pc-kflat-complex`
- `def-pur-sheaf-tensor-product`
- `lem-sf-proetale-constructible-origin`
- `prop-compactification-coherence-detailed`
- `def-coef-normalized-dvr-tower`
- `lem-fix-compact-support-coefficient-change`
- `lem-pc-quasi-isomorphisms-multiplicative-system`
- `lem-coef-normalized-dvr-effectivity`

The explicit K-flat change-of-rings and normalized-DVR-effectivity construction is
already packaged by the existing normalized chosen-reduction theorem. Integral
constructibility is supplied by its existing exact-tower theorem. The older origin
and compactification-coherence interfaces are replaced by the finite-ring intrinsic
origin theorem and the existing etale compactification-independence isomorphism,
transported through the canonical coefficient realization. No claim is made that
these removed modules leave the whole target closure. Retained
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`,
`Sheaf.Paper.CompactificationCoherence`, and
`Sheaf.Paper.IntrinsicFiniteTorsionConstructibility` as proof-only imports because the
preflight identifies them as unit-route modules.

Removed obsolete tool approvals for exactly the old direct dependencies omitted from
the final proof. The new uses of the existing finite-ring origin, chosen finite action,
and etale independence interfaces are auxiliary tools for the same source argument;
maintainer approval, if required, remains the maintainer's responsibility. No unit
statement or realized step is bypassed. The item unit has no realized steps, but the
three retained imports realize other unit routes and are preserved.

## Where the brief, the DAG or earlier work was wrong

The old plan needlessly reconstructs the chosen tower normalization and integral
membership already available as named declarations. More care is needed than plain
uniqueness of derived-limit objects: an arbitrary isomorphism does not preserve the
projection. The proof instead constructs a morphism of the two Roos triangles with
identity product components, which supplies the needed projection equation.

The resumed session rechecked the retained proof against current sources and compiled it
successfully on the server. Temporary scratch diagnostics are not delivery files. The retained DAG copy also used
`def-weil-derived-scalar-extension-restriction-adjunction`, which does not exist; corrected
it to `lem-weil-derived-scalar-extension-restriction-adjunction` in all proof uses.

Edge cases checked in the proof: positive finite levels use n+1; empty/zero objects and
d=0 need no exceptions; min/max cohomological endpoints produce an ordered interval
without assuming an arbitrary choice of endpoints is ordered. No separatedness of the
structure morphisms of X or Y is added. The dense-refinement ambient scheme inherits
finite type and quasi-compactness through its proper map to Y. Characteristic
invertibility is derived from the supplied finite-field datum and ell different from p.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
