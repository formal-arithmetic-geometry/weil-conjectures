## What changed

Proved the three original holes in `Sheaf.Paper.ExplicitExceptionalPreservation`.
The ordinary scalar adjunction uses the existing generator-normalized tensor adjunction;
extension of its unit formula proves uniqueness. The derived adjunction is constructed
from the universal counit and K-flat resolutions, and its normalization determines its
unit by naturality and localization. The preservation proof uses exact cohomology,
etale constructible origins, fixed-scalar Tor transport, and the existing finite scalar
extension API. The specified coefficient comparison is invertible by adjunction conjugation.
Private proved helpers make these identifications explicit. Existing proved private
helpers are reused through proof-only `import all`, including constructibility
invariance under isomorphisms; no duplicate public API is introduced. All existing public signatures,
definitions and public imports are unchanged. The DAG proof and dependencies now describe
this route. There are no new modules, public declarations, axioms or nodes. Proof elaboration
keeps the existing derived-functor witnesses irreducible locally and uses transparency
settings to avoid unfolding their large localization terms. The instance search size is
4096; no compilation time limit is raised. The derived-adjunction application
explicitly supplies its universe-sensitive smallness and standard-localization instances.
A full-file scratch validation of that application compiled in 53.3 seconds; its sole
style warning was then corrected in the delivered source.

## Proved and sorry left

Closed the original holes in:

- `AlgebraicGeometry.Scheme.explicitReductionModuleAdjunction_existsUnique`.
- `AlgebraicGeometry.Scheme.explicitReductionAdjunction_existsUnique`.
- `AlgebraicGeometry.Scheme.explicitExceptional_preservation`.

All three belong to `thm-exc-explicit-preservation`. The item contains zero `sorry`s;
this delivery adds zero holes and splits off zero statements. Existing imported results
remain the work of their own nodes; this is a proof from those declarations, not a claim
that the entire targets' axiom closure has become sorry-free.

## No longer needed

The following original proof imports were removed (their declarations are retained in
the shared library):

- `Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction`.
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage`.
- `Sheaf.Paper.ProEtaleFixedModuleLocalConstancy`.
- `Sheaf.CategoryTheory.SiteInverseImageTensor`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`.
- `Sheaf.Paper.FiniteTensorConstructibleCohomology`.
- `Sheaf.Paper.FiniteCoefficientFlatModel`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`.
- `Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.AlgebraicGeometry.ProEtalePullbackLocallyConstant`.
- `Sheaf.Paper.FiniteTorAmplitudeSites`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`.

The parent no longer uses `lem-exc-bounded-flat-pullback-test` or
`lem-exc-unbounded-coefficient-pullback-model`: the existing derived inverse-image Tor
API and Mathlib's conjugation of composite adjoints give those conclusions directly.
The separate tensor-cohomology and quotient-label assembly
(`lem-pur-finite-tensor-constructible-cohomology`,
`lem-exc-finite-quotient-constructible-reduction`) is replaced here by the existing
`det-sp-scalar-extension-functor` preservation API. Some underlying tensor results
remain transitive dependencies of that API; no whole-library deletion is requested.
The parent also no longer directly uses flat-model existence, local-constancy pullback,
constructible-preimage, or site-inverse-image-tensor nodes. Those arguments are already
packaged in the existing constructible-origin/pullback and Tor APIs. Only the required
statement-level imports remain public. No source-library declaration is withdrawn. The constant-ring naturality declaration
from `prop-weil-pbc-proetale-constant-ring-map` remains used by the unchanged public
comparison definition, so this dependency is retained at statement level even though
its obsolete proof-tool approval is removed.

Removed obsolete top-level tool approvals from this parent: prop-exc-open-adjoint,
lem-weil-pbc-left-exact-site-inverse-image-tensor,
prop-weil-pbc-proetale-constant-ring-map, lem-sf-flat-model,
lem-weil-pbc-ringed-topos-flat-module-pullback,
lem-pc-bounded-above-flat-kflat-site, lem-pc-kflat-resolution,
lem-weil-pbc-ringed-pullback-preserves-kflat,
lem-weil-pbc-ringed-topoi-module-pullback-tensor and
lem-pur-finite-tensor-constructible-cohomology. Their uses inside other nodes are unaffected.
The approval of lem-sf-reduction-flat-model is kept (reviewer correction): the proof still
uses it (flatModelReduction, step 5 and proof_deps).

## Where the brief, the DAG or earlier work was wrong

The original argument is mathematically valid, but the declared route asks for longer
model calculations that existing proved categorical APIs already supply. In particular,
the specific comparison is the conjugate of an isomorphism between composite right
adjoints, so its invertibility requires no new unbounded K-flat coefficient model.
The general pullback arguments do not need the open/finite-etale or invertibility
hypotheses; the original theorem retains them unchanged. Empty schemes, zero complexes,
equal coefficient levels and degenerate ordered intervals are handled by the same
functorial arguments without additional nonemptiness or flat-quotient assumptions.
The unit's realized statement and steps are retained. The original source metadata
points into an older directory; the proof-origin record uses the current blueprint.
All cited results are existing declarations, with new private glue for their use here;
this packet contains no copy of a landed public theorem and makes no statement correction.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
