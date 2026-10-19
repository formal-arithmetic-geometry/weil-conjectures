## What changed

Proved `AlgebraicGeometry.ProEtale.spEtaleMate_transpose` using the existing proved
categorical projection-map mate square. The proof transports tensor compatibility
from left-derived comparison pullbacks to their exact-functor presentations,
identifies the recorded bounded-below comparison with its unbounded mate using
`fixedComparisonDirectImageMatePlus_counit`, and cancels the tensor comparisons.
The existing projection-map transpose formula gives the first conclusion;
functorial preservation of isomorphisms gives the second.

All existing signatures, public definitions, and public imports are preserved.
Private proved helpers handle tensor transport, the included counits, the pullback
square, and the specified direct-image comparison. The generic transport API keeps
concrete coefficient resolutions out of the final categorical calculation.
No definition repair or consumer adaptation is needed. The added functor namespace opening
and local irreducibility attribute are documented in
`coord/changes/V4-sp-etale-mate-proof-scopes.md`, as required by the static interface check.

Added the proof-only import
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjComparison`
and synchronized the node's proof and proof dependencies. Clean single-file
compilation took 20.7 seconds with no warnings. Delivery checks are recorded by the
launcher.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.spEtaleMate_transpose`
(node `lem-sp-direct-image-etale-mate-isomorphism`).
Zero holes added; zero direct `sorry` occurrences remain in the item or in new
Lean modules (there are no new Lean modules). All private helpers are proved.
The proof uses the existing named counit-normalization theorem in
`Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate`. The current source
proves that dependency; this delivery neither changes it nor adds an obligation.

## No longer needed

Removed these proof-only imports:

- `Sheaf.Paper.RingedExchangeTensorCoherence`
  (`lem-weil-pbc-ringed-exchange-tensor-coherence`): the already proved categorical
  projection/mate square supplies its needed specialization directly.
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
  (`lem-weil-pbc-comparison-pullback`): the boundary comparison square and its
  equality with the transported derived square suffice.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
  (`prop-weil-pbc-proetale-constant-ring-map`): the fixed-coefficient functors and
  their existing tensor compatibility already specify the relevant square.

The import `Sheaf.AlgebraicGeometry.ProEtaleSiteComparison` is retained because it
realizes a blueprint unit statement. Its abstract geometric-morphism construction
is not used by this fixed-coefficient calculation.

Also removed `def-weil-pbc-site-comparison-morphism` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` from the proof dependencies.
The abstract ringed-topos construction is unnecessary for this calculation.
The latter tensor node remains a statement dependency and its public import is
preserved. These are removals from this proof, not claims that no other target
uses the nodes. No blueprint unit statement or realized step is bypassed.

Removed the obsolete top-level tool approvals for
`lem-weil-pbc-comparison-pullback`,
`prop-weil-pbc-proetale-constant-ring-map`,
`lem-weil-pbc-ringed-exchange-tensor-coherence`, and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Retained the approval for the canonical normalized direct-image comparison.

## Where the brief, the DAG or earlier work was wrong

The original proof plan used the general ringed-topos exchange theorem. The source
library already proves the required projection/mate calculation and the derived
site tensor compatibility. Using those declarations gives the same canonical map
without rebuilding a general ringed square. The mathematical statement and unit
route are unchanged.

The retained attempt also encountered expensive definitional comparisons of
concrete derived tensors. Explicit tensor-component equations and a generic
coefficient transport API avoid those unfoldings; no time limit was raised and
no file or proof obligation was split off.

## New nodes

`lem-sp-categorical-projection-mate-square` records the existing proved source
lemma `CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`
in `WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate`. It adds metadata
for the categorical calculation used here, not a Lean module or a postponed
obligation. The parent node's four proof steps now follow this calculation and
the normalized bounded-below comparison. No existing definition or signature changes. The scope-only change record is
`coord/changes/V4-sp-etale-mate-proof-scopes.md`.

## Second reading by V4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
