## What changed

Reduced `AlgebraicGeometry.ProEtale.reductionCompatibilities_purity` to the strictly
smaller coefficient-unit inverse-orientation equation
`AlgebraicGeometry.ProEtale.reductionOrientation`, in the new module
`Sheaf.SecSmoothPurity.ReductionOrientation`. All existing signatures and public imports
are preserved. The unit and composition proofs are retained.

The new proved private helpers perform three substantive steps. Tensorator naturality
and the already proved generic `ExceptionalCoefficients.tensorCompatibility` combine
an inverse-orientation equation with the canonical tensor map to prove the ordinary
purity coefficient square. The comparison-adjunction counit is invertible on the scalar
extension of each intrinsic Dctf input: use its bounded ordinary origin, the finite-Tor
scalar lower bound, the derived comparison unit and the site/scalar comparison. Finally
naturality of the scalar/site comparison, ordinary purity naturality and cancellation
of the origin counits transport the ordinary square to precisely the published
`proGamma`, `proCoefficientMap` and `proLambda` equation.

Validation: `lcompile.py --all` compiled the new orientation module; the final
single-file compile of the item completed cleanly in 26.0 seconds. Both Lean files
respect the 100-character line limit.

The remaining orientation theorem has no arbitrary K, tensor map, or pro-etale origin
transport. Its docstring and node describe the common-prime-power orientation argument.
The edge cases include d=0, the zero ring, empty schemes, and nonflat coefficient maps.
Only theorem proofs, private proof imports/helpers, the new theorem/node, and the item's
proof plan change. No existing definition or statement is repaired; no consumer adaptation
is required. A conservative command-scope change record documents the closed private-helper
namespace and declaration-local instance adjustment.

Searches: LeanFinder and LeanSearch for coefficient compatibility of smooth purity and
normalized dualizing orientations found algebraic smoothness, cotangent and Kaehler
base-change lemmas, with no match. Loogle found
`CategoryTheory.Adjunction.homEquiv_naturality_left`. Mathlib grep found neither
`smoothTensorDualityMap` nor `OrientationNormalized`. Project source search found the
already proved generic tensor square in `ExceptionalCoefficientComparison` and the
origin/counit/naturality helpers in `FiniteSmoothLevelOfOrientation`; private proof
imports reuse those proofs. The other orientation-reduction declarations apply only
to uniformizer/quotient rings or cite the present purity result, so they cannot replace
the arbitrary-finite-ring unit-orientation step.

## Proved and sorry left

Closed the one original textual hole:

- `AlgebraicGeometry.ProEtale.reductionCompatibilities_purity`
  (`det-sp-reduction-compatibilities`). Its complete proof uses the new orientation step.

Added one hole, the entire proof of the public theorem:

- `AlgebraicGeometry.ProEtale.reductionOrientation`
  (`lem-sp-reduction-orientation`, new module
  `Sheaf.SecSmoothPurity.ReductionOrientation`).

The item has zero remaining textual holes; this delivery adds one elsewhere. This is a
one-for-one decomposition, not a net hole closure or an axiom-free proof of purity.
All new private helpers are proved. The previously proved unit and composition identities
are not counted as newly closed holes.

## No longer needed

No existing imports are removed and no module is withdrawn. The proof uses the already
proved ordinary finite-ring tensor square, which packages the proper/open projection
and coefficient-counit calculation. Consequently the item need not import or directly
apply these former planned proof dependencies:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
  (`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`).
- `lem-weil-pbc-finite-ring-constructible-derived-origin`
  (`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`).
- `lem-weil-pbc-ringed-exchange-tensor-coherence`
  (`Sheaf.Paper.RingedExchangeTensorCoherence`).
- `lem-cbc-extension-zero-projection-formula`
  (`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj`).
- `lem-sp-finite-ring-compact-support-projection`
  (`Sheaf.Paper.FiniteRingCompactSupportProjection`).

These are replaced at this node by the existing tensor-square and finite-level-origin
interfaces; they are not declared globally unused. Their declarations and modules remain
in the library, including dependencies of retained source-library declarations. The unit
route is unchanged. `lem-pur-finite-smooth-level-of-orientation` is used as a generic
tool for its already proved private ordinary-origin, counit and naturality helpers,
not for its quotient-level existence conclusion and not as a replacement unit route.
Its proof import adds no public interface; no new tool approval is written by this worker.

## Where the brief, the DAG or earlier work was wrong

No statement error found. Steps 4--6 need not reconstruct the generic projection
coherence: the private, already proved `ExceptionalCoefficients.tensorCompatibility`
works for arbitrary finite rings and every ordinary input. The existing public quotient
specializations do not reveal that full generality, so a private proof import is used.
Similarly, the finite-level orientation module already proves the origin and ordinary
naturality facts needed to transport the equation. The common-origin orientation
comparison remains genuine geometric work and is recorded explicitly, rather than
being hidden inside a partially sorry proof or identified with arbitrary line isomorphisms.

## New nodes

`lem-sp-reduction-orientation`: the inverse normalized orientation equation at the
coefficient unit for an arbitrary finite-ring map with a common positive annihilating
exponent. This is exactly the orientation part of proof (3), now separated from its
tensor and origin-transport parts. The Lean module is
`lean/Sheaf/SecSmoothPurity/ReductionOrientation.lean`; its statement preserves the
original geometric and coefficient normalization data. The dependency census finds no path from the new orientation node or either reused
helper node back to the item. The blueprint-wide search for
"coefficient orientation" returned no duplicate; direct source searches checked the
quotient-only and uniformizer-only comparisons. Change record: `coord/changes/X6-purity-coefficient-private-proof-context.md`; the source
census lists all three importers, each unaffected by the closed private proof scope.

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
