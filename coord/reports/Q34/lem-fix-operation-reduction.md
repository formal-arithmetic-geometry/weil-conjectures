## Worker report

Repair of immutable return 3fd42d045aac, continuing the saved repairs of
a681038a5701 and the identical earlier head 7f803a5a1185. The retained Lean packet contains the substantive F1--F5 repairs.
This retry completes their metadata and self-check, makes the finite-Tor domain
explicit, and replaces a costly auxiliary record by the equivalent existential
proposition with all its data and equations retained. The old report described the returned theorem and was replaced.
Only the item's `lean` record changes; the mathematical node is unchanged.
The module is `Sheaf.Paper.BasicOperationsCoefficientReduction`, with theorem
`WeilConjectures.basicOperationsCoefficientReduction`. All helper definitions
and structures have actual data or explicit proposition fields. The only
postponed proof is that theorem's `by sorry`.

Hypotheses and clauses, read against the current blueprint statement:

1. `l`, `[Fact l.Prime]`, `E`, `[Field E]`, `[Algebra ℚ_[l] E]` and
   `[FiniteDimensional ℚ_[l] E]` give the prime and finite coefficient field.
   `Ω`, its field/algebra instances and `[IsAlgClosure ℚ_[l] Ω]` give the
   common-stage coefficient system. `X Y`, `f`, and `hX`/`hY` give the
   schemes, morphism and invertibility of l on their residue fields.
2. Integral pullback and completed tensor use `sfIntegralConstructible`,
   `integralDerivedPullback`, `integralCompletedTensor`,
   `integralPullbackFiniteComparison` and `integralTensorFiniteComparison`.
   Good representatives and their isomorphisms are universally quantified;
   they specify the actual comparison maps, not an extra existence hypothesis.
3. Finite pullback/tensor uses `canonicalFinitePullbackTensor`,
   `pullbackTensorQuotient`, and
   `canonicalFinitePullbackTensor_quotient_condition`. All positive indices
   occur as `n + 1`; `n ≤ m` includes the identity quotient.
4. Ordinary direct image is on finite-type schemes over every field `K₀`
   with `hl₀ : IsUnit (l : K₀)`. The `Over`, `LocallyOfFiniteType`,
   `QuasiCompact` and `f.IsOver` binders express that bounded domain.
   Existence of `SfIntegralDirectImage`, its bounded constructibility,
   `IsSfDerivedComplete`, invertible `sfDirectImageReductionComparison`, and
   finite-image constructibility are explicit conclusions.
5. Integral compact support has the same arbitrary `K₀` and invertibility
   binders, plus separated finite-type qc `f`, its `Compactification`, and
   constructible input `K`. A supplied Roos triangle `(M,p,δ,hδ)` specifies
   its derived limit. The conclusions are constructibility of `M`, invertible
   `coefIntegralCompactSupportComparison`, and the displayed successive
   quotient equation. **F1:** there is no `FiniteFieldDatum`, dimension bound,
   interval `(a,b)`, or `hTor` in this clause.
6. The finite compact-support clause uses positive `m ≤ n`, a separated
   finite-type qc morphism over an arbitrary field with l invertible, and the
   finite-Tor constructible input and reduced-input predicates
   (`finiteTorConstructible`). The self-check made this domain explicit, as
   required by the finite-level sentence of the node. Its comparison
   is exactly `finiteLevelCompactSupportReductionComparison`.
7. Finite Hom has `CoefficientEvaluationCompatible` and `FiniteHomEvaluation`
   for `finiteIntrinsicReductionHom`, followed by invertibility when its
   first variable is `IsProEtaleSitePerfect`. The second variable is arbitrary.
8. Integral Hom uses `IntegralHom.TensorPresentation` and
   `IntegralHom.ReductionPresentation`, arbitrary `K,L`, and completeness
   when `L` is complete. **F2:** invertibility is followed by the complete
   tensor/evaluation counit equation and the equation for every tensor-Hom
   transpose, with no site-perfectness assumption. This is the full
   `integralHomReduction` conclusion, retaining independent site universe `t`
   and coefficient universe `u`.
9. Integral scalar pullback/tensor/Hom comparisons and their naturality,
   identity and tower equations use `IntegralScalarOperations.Comparisons`.
   **F3:** the theorem additionally asserts ordinary-image and compact-support
   scalar isomorphisms, `directImageScalarTowerLaws`,
   `compactSupportScalarExtensionLaws`, and `coefficientOperationIdentityLaws`.
   These are equations for the published `PurCompactSupport.properComparison`
   and `PurCompactSupport.comparison`, which are natural transformations.
10. **F3, rationalization:** the three rational pullback, tensor and Hom
    comparison clauses identify the actual maps with localization of the
    integral comparisons. `OperationDirectImageCoefficientAction` specifies
    integral direct image by its ambient completed-ring realization and its
    scalar beta by the actual proper mate. `OperationScalarTransport` fixes
    the two scalar models on sheafified pure tensors and by the derived
    universal counit. The existential rational action is fixed on unchanged objects and
    on every pure tensor morphism; its beta is localization of integral beta.
11. **F3, common stages:** `commonStagePullbackRepresentativeLaws`,
    `commonStageTensorRepresentativeLaws`, and
    `commonStageInternalHomRepresentativeLaws` give the actual object and
    conjugation formulas on arbitrary common-stage representatives.
    The `system` witness of `OperationDirectImageCoefficientAction` gives the corresponding
    direct-image functor, coherent coefficient maps and common-stage formula.
    Compact support uses the published `SfCompactSupportCoefficientAction`:
    its finite action is fixed, its integral beta is the tensor-unit mate,
    its rational beta is localization, and its `system` is the common-stage
    action. `operationIntegralCoefficientCoherent` additionally states its
    integral identity and three-field tower equations.
12. **F4:** `coefficientOperationMateEquations` displays both geometric
    adjunction equations for the actual direct-image coefficient mate.
    `CoefficientEvaluationCompatible` and `FiniteHomEvaluation` supply finite
    and scalar evaluation/transpose compatibility; the integral equations
    are written in full in clause 8. Integral, rational and common-stage
    tensor associativity and unit predicates refer to the canonical tensor
    comparisons. The rational tensor comparison is explicitly localized;
    integral and rational scalar squares are also explicit. Finite tensor
    associativity, unit and braiding equations remain present.
13. Exceptional adjoints are asserted only under
    `IsExceptionalAdjointAdmissibleAtIntegral`. The conclusion unpacks the
    required finite adjoint families, uniform bounds, quotient compatibility
    and every scalar comparison, including identity field embeddings.
14. **F5:** the theorem docstring now reproduces all ten DAG proof steps:
    K-flat tensor/pullback; site-perfect finite Hom; integral Hom by the
    two-term quotient resolution; ordinary image; open extension by zero;
    completed compact support; finite compact support and admissibility;
    finite-free scalar change; rationalization and common stages; mate,
    evaluation, unit and counit equations. The introductory description
    names all the actual comparisons and their bounded domains.

Dependency declarations read and used:

- `Sheaf.Paper.DerivedPullbackTensorHom`: finite, integral, rational and
  common-stage pullback/tensor/Hom and their normalized comparison maps.
- `Sheaf.Paper.SfDerivedDirectImage`: `SfIntegralDirectImage`, finite-image
  terms and the canonical `sfDirectImageReductionComparison`.
- `Sheaf.Paper.SfIntegralConstructible`: `sfIntegralConstructible` and its
  full category, inherited through the operation imports.
- `Sheaf.Paper.QcqsCompactSupportRealization`: the normalized ambient
  realization of the recorded compact-support construction, inherited through
  the coefficient-comparison imports; `CompactSupportFiniteAction` and
  `CompactSupportCoefficientAction` supply its literal rational/common action.
- `Sheaf.Paper.SitePerfectComplex` and
  `Sheaf.Paper.StrictPerfectPackageOnSite`: recorded finite site-perfectness
  and its intrinsic ringed-site presentation.
- `Sheaf.Paper.ExceptionalAdjointAdmissibility`: integral admissibility,
  `ExceptionalFiniteFieldFamily`, and the finite reduction/scalar predicates.
- `Sheaf.Paper.SfRationalizationKaroubi`:
  `sfRationalConstructibleCategory`, `sfRationalConstructibleLocalization`.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: the actual `Pair`,
  `Stage`, `stageSystem`, `integralTransition`, `ofHom` and `unitor`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`:
  `scalarReductionDerivedExtension` along the completion projection.
- `Sheaf.Paper.FiniteTorAmplitude`: the finite-Tor domain conventions.
- `Sheaf.Paper.FinitePullbackTensorComparison`,
  `Sheaf.Paper.DerivedPullbackTensorIso`: canonical finite comparisons and
  integral/rational/common associativity, unit and scalar-square predicates.
- `Sheaf.Paper.IntegralHomReduction`: the complete evaluation-normalized
  `integralHomReduction` conclusion and its tensor presentations.
- `Sheaf.Paper.FiniteCoefficientHomChange`:
  `CoefficientEvaluationCompatible`, `FiniteHomEvaluation`.
- `Sheaf.Paper.IntegralOperationsScalarExtension` and
  `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`: scalar
  comparisons, actual proper/open mates, composition and unit transports.

The current source is the statement and proof in
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-sf-pf-reduction/lem-fix-operation-reduction.md` (and `.proof.md`).
The saved packet is not an unchanged repush: its arbitrary-base compact
support, full Hom equations and added coefficient coherence differ from the
returned signature, and its metadata now records those actual declarations.

Search record retained in `searches.jsonl`: LeanFinder query "basic operations
coefficient reduction derived pullback tensor ordinary direct image compact
support internal Hom evaluation rationalization scalar extension" returned
unrelated condensed Hom and underived pullback-adjunction results. The second
LeanFinder query on canonical coefficient comparisons returned underived
pullback tensor-unit results, not this theorem. Loogle queries for
`DerivedCategory, scalarReductionDerivedExtension, finiteDerivedPullback,
SfIntegralDirectImage` and for `derivedTensor, pbcDerivedExtend,
coefficientBaseChangeHom` had no matches (project identifiers unknown).
Mathlib grep `derived.*[Tt]ensor.*[Pp]ullback` in CategoryTheory returned no
match. Project `rg` inspection found the canonical operations and comparisons
above, which are imported rather than copied. This retry read the recorded
dependency signatures/docstrings and the compact-support action structures.
No new independent mathematical notion or dependency module was needed.

Edge cases checked: arbitrary base fields (not just algebraic closures of
finite fields); no external Krull-dimension/Tor hypotheses on integral compact
support; `m = n` and identity coefficient embeddings; all positive quotient
levels, with index zero representing exponent one; arbitrary second finite-Hom
variables; arbitrary first integral-Hom variables; repeated stages in
three-field towers; zero complexes and empty schemes; independent site and
coefficient universes in integral Hom. No statement correction is proposed.

## Second reading by Q34

Author self-check under the dispatcher brief; the maintainer supplies the
independent review. Read the node, current blueprint, module, saved old signature,
and return findings F1--F5 together. F1 is repaired by arbitrary `K₀` and removal
of `D/hd/a/b/hTor` from integral compact support. F2 is repaired by both full
integral evaluation and transpose equations. F3 is repaired by actual scalar
mates, their identity/tower laws, localized comparison formulas and normalized
common-stage coefficient actions. F4 is repaired by explicit mate unit/counit,
Hom evaluation/transpose, and integral tensor associativity/unit equations.
F5 is repaired by all ten proof steps in the theorem docstring. This retry also
found and fixed the stale `lean.statement`, missing `lean.declarations` helper
inventory, and the stale report. Definitions have no postponed data and the
only theorem proof remains `sorry`. Compilation and prescribed delivery checks
are performed below through the authorized wrappers before push.

The first dry run and its server confirmation both timed out at 60 seconds.
A full-file diagnostic copy located costly automatically generated auxiliary
lemmas of `OperationDirectImageCoefficientAction`. It is now an existential
proposition carrying exactly the original fields and all their equations,
avoiding the unused constructor/no-confusion/size lemmas. No file was split,
no timeout increased, and the final module contains no diagnostic commands.

Previous packet validation: `scompile.py Q34 lem-fix-operation-reduction` compiled that
module against current server sources in 52.7 s (nice 19, two threads, limit
60 s), with no diagnostics. The wrapper first timed out on its overlay path
and then returned success from the prescribed authoritative confirmation.
The final self-check verified verbatim `lean.statement`, the then 16-declaration
inventory, no lines over 100 characters, exactly one theorem `sorry`, no
diagnostic commands, and no node changes outside `lean`.

## Timeout repair of 3fd42d045aac

The prescribed initial dry run of the saved packet failed with the same 60-second
file timeout, both through the overlay and its server confirmation. A full-file
scratch copy with Lean's profiler identified the redundant elaboration of
`commonStageInternalHomRepresentativeLaws` as the largest completed command:
21.6 seconds on the overlay, versus 3.4 seconds for pullback and 2.5 seconds for
tensor. The trace shows repeated definitional-equality checks between the
coefficient modules at `L` and at the common-stage subtype containing `L`.

The repair reuses the exact predicates already published by the dependency's
`commonStageDerivedPullback_existsUnique`, `commonStageDerivedTensor_existsUnique`
and `commonStageDerivedInternalHom_existsUnique`. Each predicate is evaluated
at the same published functor. The transparent helper `operationUniqueSpecification`
is literally `P x`, with its predicate inferred from the type of the unique
characterization. It neither asserts the characterization nor replaces it with
existence or an arbitrary map. The proof argument is not inspected or chosen
from; all object equalities and all representative conjugation equations remain
in the predicate. This is an owning-module elaboration helper, with its source
and blueprint docstring and an entry in `lean.declarations` (now 17 entries).

Author self-check read the three imported characterization signatures beside
the saved formulas: their object formulas, every representative, all common
extensions, compositum bounds, contravariance for Hom, canonical scalar maps and
identity cases coincide verbatim after substituting the canonical functor for
`F`. The main theorem signature is unchanged, and the mathematical node still
changes only in `lean`. There is still exactly one postponed theorem proof;
no file was split and no limit was raised. The profiler copy is outside `lean/`
and is not delivered.

Repair validation: the prescribed `scompile.py` compiled the repaired full file
without diagnostics in 30.9 seconds at its sandbox path and 45.8 seconds at its
library path (nice 19, two threads, unchanged 60-second limit). The self-check
confirmed the verbatim theorem signature, all 17 declaration entries, exactly
one theorem `sorry`, line widths at most 100, and no diagnostic commands.
