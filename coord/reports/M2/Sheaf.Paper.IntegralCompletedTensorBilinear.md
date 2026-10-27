## What changed

Proved `WeilConjectures.integralCompletedTensor_bilinear` in
`Sheaf.Paper.IntegralCompletedTensorBilinear`, retaining its complete public signature,
public imports, coefficient action, and normalized tensor functor.

Private proved helpers transport the canonical scalar sections through the finite
projection, prove finite tensor linearity by sheafification and tensor balancing, and
obtain the other variable through the symmetric braiding. The total tensor and Roos
construction preserve these equations. A general pair of proved natural isomorphisms
for partial composite bifunctors avoids expanding the concrete Roos construction
during conversion checks; this keeps the proof within the file time limit. The good-representative comparison then descends
separate additivity and linearity, and the final nested linear map is the composition of
the two partial arrow maps. Functoriality identifies this composition with the published
simultaneous arrow action.

Proof imports reuse the already proved private constant-action and Roos helpers in
`IntegralDerivedPullbackLinear`, the localization and biproduct descent helpers in
`IntegralScalarExtensionWellDefined`, and the canonical scalar structure in
`IntegralConstructibleLinear`. They also provide the total-bifunctor linearity and
independent-universe sheaf tensor interfaces. Every added definition is an explicit
construction; no new choice of a tensor or coefficient action is made. The node proof
and its dependencies now describe this implementation. No other existing module or
node is changed.

Validation: remote single-file compilation passed in 33.9 seconds, with no proof
holes or compiler errors. Profiling options were removed for delivery. The theorem
signature is byte-identical to the original. The argument applies to all ambient objects: zero objects and maps, zero scalars, torsion
inputs, and arbitrary schemes require no cancellation or additional hypotheses.

## Proved and sorry left

Closed the sole original hole, `WeilConjectures.integralCompletedTensor_bilinear`
(node `lem-sf-integral-completed-tensor-bilinear`): 1 of 1 original holes.
No holes remain in the item and none are added or split off. Existing dependencies
retain their own proof obligations; this delivery does not claim to close those.

## No longer needed

None. Both original public imports and all five original planned dependency nodes remain
needed. The two added dependency entries record reuse of the already implemented scalar,
Roos, localization, and biproduct helpers. The alternative reflector tensor model was
not used, and no module on that route is imported. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement repair was necessary. The DAG described the descent through arbitrary
roofs; the implementation uses the existing localization API instead: additive
partial functors descend by preservation of binary products and zero maps, and scalar
linearity descends by `Localization.functor_linear_iff`. Essential surjectivity then
replaces the fixed good representative by any ambient derived object. This implements
the stated route without another split of the bilinearity obligation.

## Second reading by M2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
