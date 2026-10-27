## Worker report

The module `Sheaf.Paper.WeilTensorComparisonRationalDescent` states the two parts of
`lem-wf-tensor-comparison-rational-weil-descent`, with `sorry` proofs:
`WeilConjectures.WfTensorComparison.rational_descent` and
`WeilConjectures.WfTensorComparison.common_stage_descent`. All auxiliary definitions have
real data. They organize the hypotheses and their canonical constructions in this node's
module; they introduce no independent mathematical notion and no new DAG node.

Hypothesis and clause correspondence:

- `D : FiniteFieldDatum.{u}` supplies the prime p, positive a, q=p^a, finite base field and
  algebraic closure. `c : D.CoefficientDatum` supplies the prime ell different from p and
  the algebraic closure of Q_ell. `E : Padic.FiniteCoefficientFields c.l c.Qbar` is a finite
  intermediate extension, not a finite set. The coefficient ring and uniformizer are the
  existing `pbcStageDatum` and `pbcStageUniformizer`, on the canonical Shrink/ULift models
  of the valuation ring. Those equivalences do not change coefficient extensions.
- `W₀ : Over (Spec (CommRingCat.of D.k₀))`, `[IsSeparated W₀.hom]`,
  `[LocallyOfFiniteType W₀.hom]`, and `[QuasiCompact W₀.hom]` express exactly a separated
  finite-type scheme over k₀. `D.geometricFiber W₀` is W, with no extra smoothness or
  properness assumption. These are explicit section variables, and autoImplicit is false.
- `Integral` is the dependency's `PbcBoundedConstructibleComplete` on that geometric fiber
  with its actual completed coefficient sheaf. `Rational` is exactly `PbcRationalCategory`
  for the same datum and uniformizer; its Hom modules are raw scalar localizations.
- `ambientOrdinary` is the published `wfOrdinaryDerivedTensor`. `completion` is the
  published `wfCompletion`, with the singleton actual uniformizer and
  `wfUniformizer_generates`. `completeInclusion` only forgets the completeness property.
- `Closure.ordinary` and `Closure.completed` are precisely the assumption that ordinary
  tensor and tensor followed by completion take their values in the integral constructible
  subcategory. `ordinary` and `completed` restrict those actual ambient functors by
  `ObjectProperty.lift`. Thus their maps are the ambient maps, not arbitrary arrows or
  replacement tensor operations. Full-subcategory restriction supplies bifunctoriality.
- `transport` is `pbcIsoIntegralPullback` along `D.geometricFrobenius W₀`, the geometric
  Frobenius coefficient transport in `def-wf-weil-category`. Its rationalization is the
  existing `weilFrobeniusPullback`.
- `ordinaryMu` restricts the existing `proEtaleCanonicalTensorComparison`, with
  `wfTensorModel` on both sides and the actual completed coefficient identification.
  `completedMu` composes `wfPullbackCompletion` with completion of `ordinaryMu`. These
  are exactly the prescribed ordinary and completed comparisons in the node. They are
  constructed definitions, not extra assumptions about unspecified comparisons.
- `IntegralData.chi` records natural invertibility. `IntegralData.unit` forces each
  underlying component to equal `wfCompletionUnit` of the actual ordinary tensor object.
  It cannot be rescaled or replaced by some unrelated natural isomorphism. `compatible`
  is exactly the displayed integral Frobenius square, in Lean's left-to-right composition.
- `RationalData` packages this integral hypothesis and the two prescribed raw extensions.
  The existing `IsRawExtension` gives unchanged objects, separate linearity over the
  localized coefficient ring and the all-scalars pure-tensor formula. Inverse powers
  yield exactly the denominator r+s convention. No injectivity of integral Hom modules
  into the rationalization is assumed. The published interface is used directly.
- `component` is literally `pbcRationalization.mapIso integral.chi`, conjugated only by
  the raw-extension object equalities. `rationalMu` likewise rationalizes the prescribed
  integral comparison, using those object equalities. Both components are fixed data.
- `rational_descent` first quantifies over ALL rational f,g and gives naturality. Its
  second clause quantifies over `K L : WeilD D c W₀ E`; by the dependency definition,
  these consist of arbitrary rational carriers and arbitrary rational Frobenius
  isomorphisms. No integral lift of either structure map is an input, let alone an
  invertible integral numerator. `ordinaryPair` and `completedPair` use exactly mu
  followed by the tensor of these two structure isomorphisms. The displayed equality is
  the node's rational equivariance equation. The existential isomorphism of Weil pairs
  has hom equal to the localized actual unit and inv equal to its inverse; its isomorphism
  laws include both inverse composite identities and the inverse's equivariance.
- `common_stage_descent` assumes `d` at every finite intermediate field. It quantifies
  over any input fields E,F, any common field L, inclusions hE,hF, and any input Weil
  objects K,N. The two inputs are transported by the dependency's actual
  `weilScalarExtension`. The specified e at L has hom and inv equal to the component
  and inverse there. The further isomorphism eQ has hom and inv equal to the stage
  inclusion's maps of these two arrows, hence is precisely the inverse pair of
  common-stage classes. `StageSystem.ι` constructs such classes by `PairCategory.mkHom`
  and the normalized identity transition. Neither strict inclusions nor unequal fields
  are assumed. There is no assertion comparing components from two different L's.

Dependency declarations read and used:

- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing`, and its imported
  `Sheaf.NumberTheory.Padics.CoefficientExtension` constructions of the absolute value,
  integers, uniformizer, quotient rings and quotient transitions.
- `Sheaf.Paper.PbcWeilCategory`: `WeilConjectures.WeilD`, `weilFrobeniusPullback`,
  `weilScalarExtension`, `weilScalarSystem`, `WeilDQbar`. Their actual integral transport
  is read in `Sheaf.Paper.PbcAutomorphismTransport.pbcIsoIntegralPullback`.
- `Sheaf.Paper.WeilTensorProduct`: `wfOrdinaryDerivedTensor`, `wfTensorModel`,
  `wfUniformizer_generates`, and the completed comparison construction. The canonical
  pullback comparison is `AlgebraicGeometry.Scheme.proEtaleCanonicalTensorComparison`
  from `Sheaf.Paper.ProEtaleCanonicalTensorPullback`.
- `Sheaf.Paper.IntrinsicCompletionCompleted`: `completedKoszulUnitComplex`,
  `completedIntrinsicCompletionMap`, `IsCompletedIntrinsicallyDerivedComplete`.
  Its coefficient-presentation transport in `Sheaf.Paper.IntrinsicCompletion` is reused
  by `wfCompletionUnit`; `wfCompletion`, `wfCompletionUnit`, and `WfIsComplete` are in
  `Sheaf.Paper.WeilCompletedTensorReflector`. No completion model is reconstructed.
- `Sheaf.Paper.PbcRationalCategory`: `PbcRationalCategory`, `pbcRationalization`;
  `Sheaf.CategoryTheory.ScalarLocalization`: `ScalarLocalization`, `localization` and
  its bilinear composition. The scalar-first Hom tensor order is the published one.
- `Sheaf.CategoryTheory.BilinearCoefficientDescent`:
  `CategoryTheory.BilinearCoefficientDescent.IsRawExtension` and `IsSeparatelyLinear`.
  These specify the prescribed raw action; no duplicate generic extension definition
  is made in this delivery.
- `WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `Endofunctor.IsoAlgebra.mk`, `.carrier`, `.str` and the category of commuting maps.
  `WeilConjectures.CategoryTheory.StageSystem.Basic`: `StageSystem.ι` and its actual
  `PairCategory.mkHom` representation and common-stage composition.

Edge cases checked before writing: zero and empty-scheme objects remain allowed; tensor
closure is an explicit conditional hypothesis rather than an unconditional assertion;
rational arrows may have torsion integral representatives; Frobenius numerators need not
be isomorphisms; denominator exponent zero is included by the all-scalars raw formula;
E=F=L and identity inclusions are explicitly permitted; arbitrary finite upper fields,
not just the compositum, are allowed. The small pro-etale site's object/Hom universe
convention is inherited unchanged. No identification of those universes is imposed.

Searches actually run (full responses are in searches.jsonl):

1. msearch leanfinder: "An integral natural isomorphism of bilinear tensor functors
   localizes and intertwines arbitrary rational Weil structures". Eight hits, principally
   Localization.Monoidal.tensorBifunctorIso, lifting₂CurriedTensorPre_iso,
   tensorBifunctor, curriedTensorPreIsoPost and IsLocalization.moduleTensorEquiv.
   No hit states this actual completion-unit/Frobenius/common-Weil-stage assertion.
2. msearch loogle: "CategoryTheory.Localization.Monoidal.tensorBifunctorIso". One hit;
   its source signature was read. It identifies the localized monoidal tensor, rather
   than comparing these two tensors or arbitrary rational Weil structures.
3. msearch grep: "tensorBifunctorIso|IsoAlgebra" in CategoryTheory. Four hits, all the
   tensorBifunctorIso definition and uses in Localization/Monoidal/Basic.lean.
4. msearch leansearch: "Natural isomorphism of bilinear functors descends to scalar
   localization and intertwines Frobenius structures". Eight hits including
   LinearMap.extendScalarsOfIsLocalizationEquiv, Localization.isoUniqFunctor,
   Localization.liftNatIso, and finite-presentation module localization; none states
   the node's comparison.
5. rg in lean/WeilConjectures and lean/Sheaf for rational/comparison and bilinear
   scalar-localization patterns. Read the existing WeilTensorProduct implementation
   (its private scalarLocalization_bilinear_naturality handles a fixed tensor's
   pullback comparison), ScalarLocalizationMonoidal, BilinearCoefficientDescent,
   TensorComparisonLocalizationDescent, and PointFieldTensorDescent. Their generic or
   differently normalized assertions do not state this node. The reusable
   IsRawExtension interface is imported. Exact node-id grep in WeilConjectures gave
   no match; no existing declaration of the full item was found.

No statement correction, dependency repair, disputed statement, or new node is needed.
The natural-language proof in each theorem docstring follows the six accepted DAG steps.

## Second reading by Q71

A second pass reopened the node and the completed source and checked each item above.
This is a worker self-check: the dispatcher explicitly forbids starting other agents;
the maintainer's separate review remains independent. No independent reader is claimed.

The pass checked that chi is pinned to wfCompletionUnit, that both mu definitions are
canonical instead of arbitrary assumed isomorphisms, that rational naturality quantifies
over all arrows, and that the common-stage result uses WeilD and weilScalarExtension,
not merely the underlying coefficient category. Both inverse components are specified.
No unit hypothesis, closure hypothesis, or common-field case was dropped. The initial
compile exposed an implicit-parameter call in transport and a pipeline parse error in
the common-stage endpoint; both were repaired. A later check caught a long line and
unnecessary unfolding of the tensor model; those implementation issues were repaired.

The final equivariance equality expands both tensor Frobenius maps as the prescribed
mu followed by tensor of K.str and L.str. Component equations for the Weil isomorphism
use HEq solely to keep these definitionally identical carriers folded during
elaboration; they identify the exact hom and inverse, with no quotient or weakening.

Final compilation repair: disable asynchronous elaboration (`Elab.async false`) and
keep the canonical completion and comparison implementations folded. The diagnostic
commands were removed. Both sandbox and actual module compiled cleanly under the
unchanged 60-second limit; the final dry run compiles the exact delivery again.
