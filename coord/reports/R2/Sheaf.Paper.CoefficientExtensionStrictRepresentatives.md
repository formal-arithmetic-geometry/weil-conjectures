## What changed

Replaced the body of `WeilConjectures.coefficientExtensionStrictRepresentative_exists`
by a reduction to three separate steps of its existing argument. Its signature,
universes, public imports and all definitions used by that signature are unchanged.

`CoefficientExtensionOrdinaryStrictTensor` contains the existing private ordinary
projection constructors, moved from the item without changing their mathematics.
Its evaluation comparison now composes the existing canonical
`integralScalarReductionIso`, avoiding a large objectwise transport rewrite.
Large canonical functors are locally irreducible during elaboration.
It also contains new, proved private constructions of the degreewise `direct`
functor and `directEvaluation`; those constructors compiled before this reduction.
The remaining ordinary obligation is identification of its transition on every
section, not construction of its finite objects. The standalone ordinary existence
statement isolates precisely that first step.

`CoefficientExtensionStrictDerivedComparison` isolates the natural derived model
and its specified finite evaluation equation, given an already strict ordinary
model. `CoefficientExtensionStrictTensorNormalized` isolates normalization on a
single good representative, given that model's actual transitions. Neither asserts
the original combined existence statement.

The item proves normalization is invariant under isomorphism by naturality of the
actual derived transitions. It proves every ambient derived object has a good
representative using `exists_isKFlatResolutionIndependentCoefficients`, transports
its exact tensor-right flatness through `siteSheafTensorRightIso`, and inverts the
resolution quasi-isomorphism. Its final proof transfers normalization from the
strict representative to the specified derived coefficient extension and then to
an arbitrary object. In particular the universal quantifier over all ambient
objects is proved here, not passed into a replacement hole.

Only private implementation was relocated. The two external users of the public
theorem are `Sheaf.Paper.CoefficientExtensionReductionModel` and
`Sheaf.Paper.IntegralScalarTowerEffectivity`; neither needs adaptation.

## Proved and sorry left

This is a decomposition, not a complete proof: initial item holes 1, final item
holes 0, holes added 3. It does not claim net sorry progress.

The old hole at `WeilConjectures.coefficientExtensionStrictRepresentative_exists`
is replaced by a complete combining proof. The proved private helpers are
`coefficientSequenceNormalized_of_iso` and `coefficientExtensionGoodRepresentative`.
The ordinary degreewise constructions `scalarCoefficientDirect` and
`scalarCoefficientDirectEvaluation` are also complete and contain no `sorry`.

Every hole left in the packet is exactly a named public theorem with body
`:= by sorry`:

- `WeilConjectures.coefficientExtensionOrdinaryStrictTensor_exists`, node
  `stage3-pur-extension-ordinary-strict-tensor`.
- `WeilConjectures.coefficientExtensionStrictDerivedComparison`, node
  `stage3-pur-extension-strict-derived-comparison`.
- `WeilConjectures.coefficientExtensionStrictTensor_normalized`, node
  `stage3-pur-extension-strict-tensor-normalized`.

Validation: all four modules passed `lcompile.py`. The final assembly passed after
introducing the normalization indices explicitly; the ordinary construction uses
the public canonical tensor comparison to avoid broad congruence and transport
rewrites. Debug profiling options are removed. The final ordinary implementation compiled
cleanly in a reported 14.0 seconds; the final assembly compiled cleanly in the
preceding two-module check. The mandatory delivery tool performs the final
preflight and axiom checks.

## No longer needed

No mathematical node or library module is claimed pruned. No unit route is changed.

The item's proof imports `Sheaf.CategoryTheory.SequenceProjectionDerivedAdjunction`
and `Sheaf.Paper.IntegralScalarExtensionWellDefined` have moved, with their private
ordinary constructors, into `CoefficientExtensionOrdinaryStrictTensor`. The latter
now uses its public canonical comparison instead of private transport lemmas. They remain
needed there; this is not removal from the targets' closure. The original derived
calculus, semilinear calculus and change-of-rings K-flat dependencies remain in the
new sublemmas' proof plans. The item directly uses K-flat resolution and the three
new steps instead of treating those lower ingredients as if they supplied the whole
argument in one application.

## Where the brief, the DAG or earlier work was wrong

The recorded dependencies supply ingredients rather than the simultaneous natural
model-evaluation identity and the normalization calculation themselves. Steps 2
and 3 of the original node had no `uses` entries despite being non-elementary.
They now have independently stated, strictly partial obligations. The earlier
ordinary private scaffolding stopped before the degreewise functor, its evaluation,
and the transition verification; the first two are constructed in this packet.

No false statement or definition repair was found. In particular no finite
coefficient ring map is assumed flat; the proof plans use good representatives,
including ramified extensions and unbounded complexes. Edge cases checked in the
new statements: zero complexes are included, m=n uses identity, n=0 denotes the
first positive quotient as in the existing library, and site and coefficient
universes remain independent. The generic comparison permits any compatible strict
model: its actual successor equations provide the chain-level coherence needed
before localization; it never infers equality of arbitrary derived maps from
joint conservativity.

The current `literature/blueprint/latest` version of the operations definition
places coefficient compatibility in `sk-prop-scalar-six`. The assignment's older
node still records its integral-operations source. The exact assigned interface
is retained. The new nodes expand its three recorded proof steps, using the same
Stacks ingredients (03D7 ordinary adjunction, 06YY K-flat pullback, 07A6 derived
adjunction and 0941 sequence-site limits), and do not change a blueprint unit.

## New nodes

`stage3-pur-extension-ordinary-strict-tensor` is the ordinary strict tensor-model
existence and its all-section quotient transition formula. It contains no derived
comparison or normalization claim. Its module preserves the ordinary constructors
and adds the degreewise constructors to assist the next worker.

`stage3-pur-extension-strict-derived-comparison` supplies only the natural model
and exact evaluation equation after the ordinary model has been supplied. Its
proof plan constructs and derives the adjunction comparison before using finite
conservativity for invertibility.

`stage3-pur-extension-strict-tensor-normalized` supplies normalization only on a
specified good representative. Balanced association computes the transition
adjunct and the tensor/restriction Hom criterion proves its bijectivity. The
extension to arbitrary derived objects is proved in the original item.

Searches: LeanFinder returned ordinary tensor presentations, LeanSearch returned
ordinary `ModuleCat.extendScalars_assoc` and related scalar coherence, and Loogle
found no simultaneous derived statement. Source grep found only the joint
unproved item, its existing ordinary scaffolding, and consumers accepting an
already strict model; Mathlib's `mapHomologicalComplexCompIso` supplies the standard
degreewise comparison ingredient. Each new node records these searches.

The proved `NormalizedOperationSystemModels` helpers were also checked. Their pull
normalization theorem requires an already normalized input and the geometric
pull-transition interface; it does not directly normalize this tensor construction
from an arbitrary integral complex.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
