# Single-level intrinsic comparison and its two normalization results

## Reason

The remaining evaluation argument combines two distinct source results: exact
termwise evaluation of the clopen alpha, and finite etale scalar/site
normalization of its single-level proper mate. State those results on an
independently constructed single-level comparison, so neither merely renames
or repackages the full tower-and-origin evaluation assertion.

## Old

No declaration with these new single-level names existed. No existing
signature or data definition is changed.

## New

SingleProperOpenArrows constructs singleOpenToR and singlePi from the specified
module adjunctions, constructs singleAlpha from canonical cartesian open base
change and the clopen projector, descends the exact transformation using
Localization.liftNatTrans, and takes its proper-adjunction mate singleGamma.
Invertibility of the ordinary open unit, cartesian singleBetaInv and clopen
singleOpenToR are proved for arbitrary B. The private fixed-coefficient helpers
of StrictTowerProperOpenArrows occur only in theorem proofs, never in public
definition bodies or public signatures. There is no data hole or arbitrary
choice of an interchange transformation.

StrictTowerAlphaEvaluation states the exact evaluation square for alpha. It has
no proper direct-image functor, finite ring, origin witness or origin isomorphism.
StrictTowerGammaEvaluation proves its proper mate square by the existing proved
coefficient_exchange_of_counit theorem and four mateEquiv_counit equations.

SingleProperOpenFiniteNormalization states the canonical finite etale
normalization for singleGamma. It has no strict tower or evaluation index.
The finite arrow is exactly the nested witness of
properOpenInterchangeCoherence, and both canonical module comparison isomorphisms
are explicit composites of hJ and hR. This is the bounded-below finite comparison
part of the source argument, rather than the full tower-origin theorem.

The two normalization theorems are the only new holes. The item combines them
by proved mate pasting, naturality along originIso and a generic isomorphism
transport calculation. Identity squares and empty opens satisfy both statements:
all comparisons reduce to their normalized identities or maps of zero objects.
For a cartesian square, the alpha square specializes to the existing normalized
beta evaluation equation; the arbitrary-B open comparison needed here was proved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleProperOpenArrows | U3, new | Actual single-level construction; zero holes. |
| Sheaf.AlgebraicGeometry.StrictTowerAlphaEvaluation | U3, new | One exact-evaluation source lemma. |
| Sheaf.AlgebraicGeometry.StrictTowerGammaEvaluation | U3, new | Complete proper-mate proof from alpha evaluation. |
| Sheaf.AlgebraicGeometry.SingleProperOpenFiniteNormalization | U3, new | One finite scalar/site normalization source lemma. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | U3 | Complete origin-transport proof of gamma_evaluation from the two lemmas. |

No existing consumer is adapted. Existing target statements and definitions
retain their meaning. These new dependencies require independent proof review.

## Status

landed 20261021T024203-L-3042570 2026-10-21 (merge of deliver/U3/Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus)
