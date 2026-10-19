## What changed

Retained the earlier attempt and proved the coefficient-presentation bridge rather
than forwarding its tensor-homology hole. The item now combines the source etale
Tor-predicate conversion, the source comparison theorem, and the intrinsic transport
lemma. All existing signatures and public imports are unchanged.

The new module `IntrinsicRealizationTensorComplex` constructs the natural ordinary
tensor comparison using module sheafification along the constant-scalar unit. It
then applies the proved source total-bifunctor comparison. The module
`IntrinsicResolutionTensorComparison` transports the supplied intrinsic K-flat
complex through the inverse equivalence, proves it K-flat by reflecting acyclicity,
and applies the source K-flat single-tensor computation. The transport module
uses that comparison for each test sheaf and degree, in both directions.

Also retained the completed proof of
`finiteCoefficientIntrinsicRealization_exact` in the unclaimed dependency module
`Sheaf.AlgebraicGeometry.ProEtaleFiniteModuleIntrinsicComparison`. Its scalar-unit
adjunction has invertible unit on fixed-scalar sheaves and essentially surjective
counit. This closes another existing hole without changing any definition.
Abstract-functor private helpers keep the canonical realization from unfolding
repeatedly in the tensor and derived-category calculations.

## Proved and sorry left

Closed the item's original hole:
`AlgebraicGeometry.ProEtale.comparison_torAmplitudeIn_iff`.
Additionally closed the existing hole in
`AlgebraicGeometry.ProEtale.finiteCoefficientIntrinsicRealization_exact`.

The three new public theorems are proved:
- `AlgebraicGeometry.ProEtale.intrinsic_realization_tensor_complex_iso`
- `AlgebraicGeometry.ProEtale.intrinsic_resolution_tensor_homology_iso`
- `AlgebraicGeometry.ProEtale.intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn`

Two existing holes closed, zero holes added. No `sorry` remains in any of the five
delivered modules. The complete sandbox passed `lcompile.py --all`; all five
modules compiled, with the slowest taking 11.2 seconds in the earlier recorded run.
On resumption, the required dry run again passed compilation of the delivered set
and proceeded to its axiom probes. These proofs use existing declarations of the
library, whose remaining proof obligations are outside this delivery.

The interval endpoints may coincide, the coefficient ring may be zero, and the
scheme may be empty; no argument excludes these cases. The tensor comparison is
for arbitrary unbounded complexes. Intrinsic transport tests every module sheaf,
and does not restrict its derived object to etale origin.

## No longer needed

Removed proof-only imports from the item:
- `Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedFlatReplacement`
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
- `Sheaf.Algebra.Homology.SiteFlatOpcyclesTorCriterion`
- `WeilConjectures.SixFunctors.ProEtale.Comparison.Flat`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Paper.PbcActualScalarPullback`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The original planned direct uses of
`prop-weil-pbc-site-comparison-finite-level`, `lem-sf-comparison-pullback-exact`,
`lem-pc-kflat-bounded-flat-replacement`, `lem-pc-bounded-above-flat-kflat-site`,
`lem-weil-pbc-site-flat-opcycles-tor-criterion`,
`lem-exc-constant-inverse-image-flat` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are replaced by the existing
fixed-scalar comparison theorem, which already proves preservation and reflection
by the prescribed flat-model/tensor route. Their top-level tool approvals were
withdrawn. General K-flat resolution existence remains needed by the transport proof;
intrinsic derived tensor remains needed by the single-test comparison. Definitions
in the statement remain needed; no public import was removed. Transitive dependencies of the source theorem may
still reach some of these modules; this report claims direct pruning only.

## Where the brief, the DAG or earlier work was wrong

The previous attempt treated the explicit etale `hasTorAmplitudeIn` and the
standard t-structure `torAmplitudeIn` as definitionally equal. Their conversion
uses the already proved source lemma in `Finiteness.FlatModel`. The existing source
comparison theorem makes rebuilding the long fixed-scalar flat-model argument
unnecessary; it already uses that route.

The interrupted work had reduced the single-test comparison to total tensor
transport, but had not supplied its DAG node or updated the report. Both records
now follow the proof. The new proof transports the given K-flat complex backwards
through the equivalence; it needs neither a new resolution of K nor a separate
resolution-independence lemma.

The initial required dry run stopped at the launcher's split-off time gate. No
new hole is now proposed. Remote compile requests initially returned no answer;
subsequent requests reached Lean and exposed ordinary universe/instance issues,
which were repaired in the sandbox.

## New nodes

`lem-exc-intrinsic-realization-tensor-complex`: natural tensor comparison and
ordinary total tensor transport. This is the chain-level input, before any
K-flatness or cohomology statement.

`lem-exc-intrinsic-resolution-tensor-homology`: single-test tensor cohomology
comparison, proved from the chain-level comparison by the inverse-equivalence
K-flat argument and the existing source single-tensor model.

`lem-exc-intrinsic-tor-amplitude-transport`: the intrinsic and standard Tor
predicates agree on every fixed-scalar pro-etale derived object. The proof uses
single-test comparisons, essential surjectivity and zero-object reflection.

No definition, existing signature, or visibility was changed, so no change record
or forced consumer adaptation is needed.

Resumption on 2026-10-19 retained and reviewed all five proof modules against
current sources. Checks confirmed unchanged existing public imports and
signatures, no `sorry` tokens, 100-column Lean lines, exact agreement between
proof-step dependencies and `proof_deps`, and verbatim node/Lean signatures for
all three new theorems. The required dry run passed compilation and server
preflight (commit `b4cce52e4e`, review class CODEX). One axiom probe, for
`ProEtaleFiniteModuleIntrinsicComparison`, received no answer from the compile
service; this is not claimed as a completed axiom audit. The delivery tool leaves
that check to the maintainer's merge and global build. The extra existing module
is unclaimed and its changes only prove its existing theorem using private
helpers; it is not a forced adaptation of another group's module.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
