## What changed

Replaced the hole in `scalarSixDirectImage` by an assembly proof. The proof derives
finite type, quasi-compactness and separatedness of the over-morphism by cancellation;
uses direct-image stability at both coefficient endpoints; proves comparison
invertibility by induction on `ListedCoefficientMap`; and obtains the four ambient
coherence assertions from `scalarDirectImageMateCoherence`.

Added two statement modules, `ListedCoefficientCtf` and
`ScalarDirectImageElementaryCases`, to isolate the missing presentation transports
and elementary cases. The composite induction is real Lean: it uses scalar
preservation for the intermediate input, the two induction hypotheses, the
coefficient-pasting identity, preservation of isomorphisms by functors, and
cancellation of the scalar tower isomorphism. Existing theorem signatures, public
imports and definitions are unchanged. No source-library module is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.CondensedRing.scalarSixDirectImage` (1 of 1 original
holes). Added two named holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.listedCoefficientCtf`, node
  `lem-sfb-listed-coefficient-ctf`: endpoint admissibility and scalar preservation
  for the actual listed coefficient presentations.
- `AlgebraicGeometry.ProEtale.CondensedRing.scalarDirectImageElementaryCases`, node
  `lem-sfb-scalar-direct-image-elementary-cases`: the six primitive coefficient
  cases and the algebraic-closure identity, with no composite-map assertion.

This is a decomposition, not a net proof: one upper hole closed, two lower holes
added, net -1 before changes in the target import closure. No sorry remains in the
item module; no new definitions or axioms are introduced. The new statements cover
zero finite rings, nonflat finite maps, arbitrary standing positive-characteristic
fields, and the identity coefficient case. They are strictly parts of the argument:
neither states the original theorem or packages its hypotheses as a new assumption.

## No longer needed

Removed these direct private imports from the item module:

- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`
- `Mathlib.AlgebraicGeometry.Morphisms.Proper`
- `Sheaf.AlgebraicGeometry.FiniteFreeDirectImageCoherence`
- `Sheaf.Paper.LocalizedDirectImageComparison`
- `Sheaf.Paper.QlbarDirectImageComparison`
- `Sheaf.Paper.CondensedModuleDerivedPushpull`

The elementary comparison modules remain needed below the new elementary-case
lemma, and the ambient module-derived pushpull interface remains available through
existing public imports. These are import removals, not claims that the underlying
mathematics is globally unnecessary. The original explicit closed-diagonal/base-change
argument is replaced by Mathlib separatedness cancellation. Thus the parent proof
no longer directly needs `lem-weil-pbc-closed-immersion-base-change` or
`def-weil-closed-immersion`; its finite-type and separatedness conclusions come
from cancellation and its quasi-compactness conclusion uses quasi-separatedness
of the target structure map. The parent node also removes its obsolete direct tool-use approvals:
`lem-sf-projection-finite-constant`, `lem-kun-0f10`,
`lem-weil-pbc-ring-sheaf-change-adjunction`, `lem-weil-pbc-mate-pasting`,
`lem-weil-pbc-ringed-projection-mate-exact`, `lem-sc-dvr-fg-torsionfree-free`,
`lem-sbc-canonical-restrict-scalars-functor-comparisons`,
`lem-sbc-restrict-scalars-derived-adjunction-identities`,
`lem-pur-etale-scalar-mate-projection`, `lem-sp-finite-free-direct-image-coherence`,
`lem-sfb-localized-direct-image-comparison`, and `lem-sfb-qlbar-direct-image-comparison`.
They are no longer direct tools of the assembly: the relevant comparisons remain
below the elementary-case lemma, as its dependency record explains.
No module is withdrawn. The parent node records the
new immediate dependencies; the new nodes retain the elementary comparison route.

## Where the brief, the DAG or earlier work was wrong

The planned applications require genuine presentation glue. `scalarSixCtf` takes
`IsListedScalarCoefficientMap`, not `ListedCoefficientMap`; its finite endpoints
use Type 0 topological presentations, whereas the item accepts finite rings in
Type u and postcomposition-normalized actual ring-object maps. The fixed-module
`finiteRingRelativeScalarComparison`, the section-module
`finiteFreeDirectImageCoherence`, and the internal-module item also have different
presentations. Their maps must be transported using the published pullback and
adjunction normalizations; an arbitrary isomorphism of outputs does not suffice.
The two new statements isolate this work without weakening any original assertion.

The unit route is retained: primitive coefficient comparisons, preservation,
coefficient pasting, and ambient mate coherence. No mathematical counterexample
or statement change is asserted.

## New nodes

`lem-sfb-listed-coefficient-ctf` supplies endpoint admissibility and transports
scalar preservation to the exact listed-map presentations. Its proof follows the
coefficient list and scalar-six-ctf clause (3), with exact scalar equivalences,
finite ring presentation changes, the identity case and scalar tower induction.

`lem-sfb-scalar-direct-image-elementary-cases` supplies only primitive comparisons
and the identity. Its proof retains finite relative cohomological dimension,
finite-free and perfect two-term models, bounded-below localization and
algebraic-closure comparisons, and normalization of the actual counit mates.
It leaves finite composite maps to the proved induction in the item.

No change record is needed: no existing signature, definition or public import
was altered, and no consumer adaptation is required.

## Second reading by B5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
