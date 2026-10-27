## What changed

The original integral compact-support theorem is reduced to five separate parts:
preservation, pullback preservation, normalized comparisons, compatible composition,
and cartesian base change. Its proof assembles all eight coherence fields from the
same witnesses; the coefficient identification is delegated to the preservation and comparison lemmas.
The interface is extracted into IntegralCompactSupportDefs and publicly re-exported.
The original functor definitions and cached instance environment are preserved verbatim.
No upstream source module is changed. See the interface change record.

## Proved and sorry left

Closed: integralLocalizingCompactSupport (1 original hole). Its body is a complete
assembly from the five separate obligations, so this delivery is a decomposition,
not a net decrease in holes. Five holes are added, each in its own module:

- preservation_of_ctf_eq: lem-sfb-total-derived-preservation.
- pullback_of_ctf_eq: lem-sfb-total-derived-pullback.
- normalizedComparisons: lem-sfb-total-derived-normalized-comparisons.
- compatibleComposition: lem-sfb-total-derived-compatible-composition.
- cartesianCompactSupport: lem-sfb-total-derived-cartesian-compact-support.

The item module has zero holes; the five declarations above are the entire remaining
hole set in this packet. Net change: one hole closed and five added (decomposition).
No definition contains a hole. Extensive proof drafts for the preservation,
composition, normalization and cartesian transport arguments are retained from
the earlier attempt; unfinished drafts are outside the delivery packet.

## No longer needed

Removed proof imports from the item: IntegralTensorInverseImage,
CompactificationCoherenceCocycle, IntegralExtensionByZero,
NonrationalLocalizingLowerShriekComposition, DetSfCompCompositionBaseChange,
ProperImageLocalizingProper, and LocalizingClosureCtfEqualsBc. The latter is
needed by the preservation and pullback obligations, but is not used directly by
the assembly proof.

The direct IntegralExtensionByZero and ProperImageLocalizingProper imports are
replaced by the existing compactification_localizing preservation package, recorded
in the preservation node. IntegralTensorInverseImage is replaced by the existing
UnboundedLocalizingPullback construction, recorded in the pullback node. The new
comparison, composition and cartesian lemmas retain the mathematical roles of
CompactificationCoherenceCocycle, NonrationalLocalizingLowerShriekComposition and
DetSfCompCompositionBaseChange. None of those nodes is withdrawn. No blueprint
unit or source-library declaration is removed. No module is claimed globally pruned.
The main node now lists exactly the five split lemmas as its proof dependencies.

Reviewer correction (cc review of 49558366): the five split-off modules no longer import
Sheaf.Paper.LocalizingAdmissibleCoefficients or Sheaf.Paper.LocalizingClosureCtfEqualsBc;
their statements use only IntegralCompactSupportDefs, and the proofs that will need these
modules are still `sorry`. The unused local instances spaceOver … mapQuasiCompact were
removed from the item module: the assembly proof does not use them.

## Where the brief, the DAG or earlier work was wrong

The canonical comparison theorem is normalized against common dense refinements;
the item instead asks normalization for every boundary-preserving refinement and
uses the total derived open adjunction. Transport between those adjunctions is a
real additional argument. The base-change dependency uses literal fibre products,
while this item quantifies arbitrary cartesian presentations. One must transport
the specified mates and their comparison equation, not choose an arbitrary
base-change isomorphism. Density is not preserved by arbitrary base change.

On resumption, the required delivery check compiled all seven modules but rejected
blank lines inside five theorem signatures. These are repaired. The retained
composition module also disabled respectTransparency; that setting was removed.
The extracted definition block was checked against the current item source: all
declarations from Ambient through Coherence and their instance setup are unchanged.

## New nodes

`def-sfb-integral-compact-support-interface` records the existing public definitions
extracted without changing their signatures or bodies. Its source is the integral
compact-support construction; the search found no Mathlib replacement for this interface.

`lem-sfb-total-derived-preservation` states the four preservation clauses. Its proof
uses compactification_localizing and the integral Dctf/Dbc equality.

`lem-sfb-total-derived-pullback` states preservation of Dbc and Loc(Dbc) by actual
inverse image, for any base field. Its proof uses the existing finite-model pullback
and localizing-closure construction; it imposes no unnecessary characteristic hypothesis.

`lem-sfb-total-derived-normalized-comparisons` supplies identity, cocycle and the
normalization against boundary-preserving refinements, with the total open adjunction.
Its source is the compactification comparison and refinement argument.

`lem-sfb-total-derived-compatible-composition` supplies composition for the given
normalized comparison family, with the simultaneous comparison equation. Its source
is the nonrational localizing composition argument and transport by the cocycle.

`lem-sfb-total-derived-cartesian-compact-support` supplies invertibility and comparison
compatibility of the specified mates on arbitrary cartesian presentations. Its source
is the existing literal-fibre-product base-change argument, transported to that presentation.

All five statements are strictly separate portions of the original conjunction;
each has a sourced proof in words, a verbatim Lean statement and recorded searches.
The main node records their assembly. The interface change is documented in
coord/changes/integral-compact-support-interface.md.

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
