## What changed

Completed the coefficient cocycle and reduced the isomorphism theorem to the normalized
coefficient/site mate equality in intrinsic coordinates. The separate intrinsic proper
coefficient theorem is proved from that equality and the existing ordinary etale proper
coefficient theorem.
The item docstring and DAG now describe this route.
Every original signature and public import is unchanged. All new item imports are
proof-only.

The isomorphism proof descends M to a bounded constructible etale L and uses exact
open extension to obtain J. It proves the lower bound on the actual scalar extension
J_B by the open scalar isomorphism, scalar preservation for M, and reflection of
cohomological intervals by the finite-ring comparison. It applies the retained proper
comparison to J and J_B and transports invertibility along the open-origin isomorphism.
For all six endpoint membership claims, it applies the existing uniform compact-support
Tor-bound theorem and scalar preservation in intrinsic coefficients. This avoids the
condensed module-object preservation interface of the earlier Step 9.

The ordinary etale scalar/pullback comparison is proved to be the inverse scalar
adjunction mate, by iterated conjugation and the restriction/coextension triangle.

The ordinary realization/restriction/direct-image square is also proved, by the three
section/unit normalization equations and bijectivity of the realization unit.

The cocycle proof is complete: tensor-unit normalization on flat-term K-flat models
identifies the scalar associator with its adjunction mate; exact restriction squares
compose on sections, and derived mate pasting gives the pullback cocycle. The proved
proper and open cocycles and a private naturality calculation assemble the result.

Validation: the final eight-module ordered compile passed without diagnostics; the
ordinary scalar normalization compiled in 8.5 seconds, the intrinsic proper proof in
19.5 seconds and the item in 23.3 seconds. The item also compiled after the docstring
update in 27.3 seconds. Both original
signatures and the original public-import set were compared verbatim with current sources.
The dry run passed with review class CODEX. Its axiom probes for
ProperIntrinsicFiniteCoefficientExtension and PullbackScalarCoefficientCocycle timed
out; the delivery tool explicitly schedules these probes again at merge. Their
standalone compiles passed, so no complete axiom-scan claim is made here.

## Proved and sorry left

Closed both original holes:

- AlgebraicGeometry.ProEtale.reductionDirectImage_cocycle, fully proved.
- AlgebraicGeometry.ProEtale.reductionDirectImage_isIso, reduced to the coefficient/site compatibility result
  below; its open, origin, boundedness and six membership steps have complete proofs.

Added exactly one direct hole:

- AlgebraicGeometry.ProEtale.intrinsicCoefficientSiteMate
  (lem-sp-intrinsic-coefficient-site-mate), the equality of the two canonical
  coefficient/site mate composites in intrinsic coordinates. It is the presentation
  version of the scalar/site cube in the finite-rings paragraph of the scalar-six
  direct-image source. Its ordinary realization square and ordinary scalar mate normalization are proved here. The remaining
  work identifies the derived scalar/pullback normalizations and takes geometric mates.
  This equality has no properness, boundedness, characteristic, constructibility or
  Tor-amplitude hypothesis, and makes no invertibility assertion.
The three new coefficient-cocycle theorems, properIntrinsicFiniteCoefficientExtension,
realizationRestrictionDirectImage, scalarSheafPullbackIso_inverseMate, and every private helper are fully proved from their
recorded dependencies. The proper proof explicitly applies the existing ordinary etale
properFiniteCoefficientExtension and cancels the invertible boundary maps of the square.
Original holes: 2; closed: 2; added: 1; remaining: 1. Thus the isomorphism part is a
reduction and the cocycle part is a proof; the packet closes one net direct hole.
The retained compatibility equality is a strictly separate coherence step of the source,
not an isomorphism theorem with its input hypotheses repackaged. The proper inference,
the open reduction, the origin and lower bounds, and all membership claims are proved
in Lean around it. Zero coefficient rings, empty schemes and non-flat
coefficient maps preserve the tensor-unit and adjunction equations used here.

## No longer needed

The old finite-cohomological-dimension/free-resolution route is replaced by the existing
proper finite-coefficient theorem, with its intrinsic coefficient/site normalization retained separately.
The old Step-9 condensed preservation result is replaced by the intrinsic uniform bound.
The original unit-route imports InjectiveModuleDirectImageAcyclic and
ProEtaleSiteComparisonFiniteLevel remain as required by the blueprint unit contract.

Removed these unused direct proof imports from the item:

- Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
- Sheaf.AlgebraicGeometry.ProEtaleOpenTensor
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
- Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
- Sheaf.CategoryTheory.RingedSliceExtensionTensor
- Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
- WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
- Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
- Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension
- Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension
- WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
- Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
- Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula
- Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction
- Sheaf.Paper.SpDirectImageEtaleMate
- Sheaf.Paper.DirectImageChangeRingTranspose
- Sheaf.Paper.FiniteLocalizingExceptionalPreservation

KFlatResolutionIndependentCoefficients is used by the proved pullback helper, although
it is no longer directly imported by the item. The proper/open cocycle requires no
separate open K-flat calculation. No module is claimed removed from the whole target
closure: the listed removals concern this proof and its route.

The replaced direct proof nodes are lem-sp-direct-image-change-ring-transpose and
lem-sp-direct-image-etale-mate-isomorphism: the existing unbounded etale proper theorem
and the single intrinsic coefficient/site equation replace that projection-transpose
route. Also no longer used directly are lem-sf-projection-finite-constant,
lem-kun-0f10, def-kun-cd, lemma-weil-pbc-leray-acyclicity and
lem-weil-pbc-module-sheaves-enough-injectives: their separate finite-CD/free-resolution
calculation is unnecessary with properFiniteCoefficientExtension. The old membership
node sk-prop-sf-rf-shriek-preservation is replaced by det-sp-tower-bound-uniform in
intrinsic coordinates. The two unit-route nodes remain imported and are not pruned.

Other removed direct node edges are encapsulated in the new factor results or their
public interfaces and remain needed transitively: prop-weil-pbc-proetale-constant-ring-map,
lem-weil-pbc-ringed-topoi-derived-tensor-pullback, def-weil-pbc-proetale-operations,
lem-trf-open-tensor, lem-cbc-proetale-extension-zero, lem-pc-kflat-resolution,
lem-weil-pbc-ringed-slice-extension-tensor, def-weil-extension-by-zero,
lem-weil-proetale-weakly-etale-localization, lem-weil-pbc-extension-by-zero-exact,
lem-cbc-proetale-extension-zero-comparison and lem-weil-pbc-ring-sheaf-change-adjunction.
They are not claimed removed from the target closure.

## Where the brief, the DAG or earlier work was wrong

The earlier packet/report described a decomposition with an unproved pullback cocycle.
That normalization is now proved. The Step-9 preservation input uses condensed
module-object coordinates, whereas this item uses intrinsic ordinary ring-sheaf modules.
The uniform compact-support Tor-bound theorem supplies exactly the needed intrinsic
preservation result, after a unit-normalized change of open coordinates.

The fixed ordinary etale proper theorem does not directly typecheck as an intrinsic
coefficient comparison. The packet now includes the complete proper inference from the
normalized coefficient/site equation and the existing proper theorem. The one remaining
normalization equation is recorded with the actual canonical maps and a complete proof
in words; no arbitrary endpoint isomorphism is selected.

The resumed dispatch reset the reference clock: the current .budget start is
2026-10-19 17:07:48 UTC. Earlier resume attempts are recorded in scratchpad logs
resume-dry-run, dry-run-resumed, dry-run-resume-latest and dry-run-http429-resume;
their elapsed counters restarted despite retained proof work. No attempt identifier
was supplied in the brief or metadata, and no launcher or budget file was edited.
Proof work continued throughout the current reference period.
Preflight required a change record for private proof-context commands and retention
of the two unit-route imports. Both diagnostics have been repaired.
The three latest nodes initially counted LeanFinder and Loogle separately; the
checker requires LeanSearch as well. All three missing searches were run and their
actual results are now recorded.

## New nodes

lem-sp-etale-scalar-sheaf-pullback-mate, in
Sheaf.SecSmoothPurity.EtaleScalarSheafPullbackMate: proved ordinary scalar/pullback
normalization by the scalar and geometric adjunctions. This closes the ordinary
scalar normalization step of the remaining coefficient/site cube.

lem-sp-direct-image-scalar-coefficient-cocycle, in
Sheaf.SecSmoothPurity.DirectImageScalarCoefficientCocycle: proved proper-factor cocycle,
by counit mates and the geometric adjunction bijection.

lem-sp-open-scalar-coefficient-cocycle, in
Sheaf.SecSmoothPurity.OpenScalarCoefficientCocycle: proved open-factor cocycle,
by inverse mates and cancellation of the intrinsic coordinate isomorphisms.

lem-sp-pullback-scalar-coefficient-cocycle, in
Sheaf.SecSmoothPurity.PullbackScalarCoefficientCocycle: proved scalar-associator/unit
normalization and its derived mate-pasting consequence.

lem-sp-proper-intrinsic-finite-coefficient-extension, in
Sheaf.SecSmoothPurity.ProperIntrinsicFiniteCoefficientExtension: the separate proper
coefficient-extension result in intrinsic coordinates, proved from the normalized
coefficient/site equality, bounded-below qcqs comparison and the existing etale proper
coefficient theorem. Both actual etale lower bounds are retained.

lem-sp-intrinsic-coefficient-site-mate, in
Sheaf.SecSmoothPurity.IntrinsicCoefficientSiteMate: the remaining coefficient/site
coherence equality, with its two canonical boundary constructions. Its proof in words
specifies the ordinary square, derived tensor-unit normalization and geometric mate
calculation; only this theorem has sorry.

lem-sp-realization-restriction-direct-image, in
Sheaf.SecSmoothPurity.RealizationRestrictionDirectImage: proved ordinary realization
square, the first normalization step of the remaining coherence result.

Proof-context change record: coord/changes/F1-reduction-direct-image-proof-context.md.
No existing signature, definition or public import changes; no forced adaptation.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
