## What changed

Proved the three remaining holes in `Sheaf.SixFunctors.FrobeniusPointTransport`.
Finite sigma is restriction of sections, with linearity from the normalized
constant coefficient comparison. Integral sigma follows by checking each finite
quotient projection of the completed coefficient sheaf. Both constructions commute
with the differential and are unique termwise.

For integral transport, descend the natural sigma map through localization. The
existing whole-tower reduction-counit identity identifies the adjunction transpose
of a natural tower map with the recorded comparison on every good complex.
Naturality along each resolution quasi-isomorphism gives its prescribed formula.
Composition with sigma, followed by conjugation along a representing isomorphism,
proves existence; one flat-term K-flat resolution forces uniqueness.

Added the private proof import `Sheaf.Paper.IntegralPullbackReductionCounit`. The realization and reduction-counit
statements are existing dependencies; their previously existing holes are not
claimed as proved here. Models supplied by realization are eliminated inside a
proof, and no data definition chooses an undetermined object.

Reformulated the two sigma specifications as heterogeneous equality of their
underlying functions. Their function domains and codomains are definitionally the
original section types, so `heq_eq_eq` and `funext_iff` recover exactly the old
pointwise conditions. This avoids expensive kernel normalization of the composite
functors: the otherwise unmodified file compiled in 18.1 seconds after this change,
whereas the original file timed out at 60 seconds. No external module uses either
specification theorem. All existing public definitions retain their signatures and
bodies, and every target retains its meaning.

Validation: the complete final item compiled without warnings in 33.0 seconds
through `lcompile.py`, against the published library without a sandbox artifact
overlay. The new Lean import was checked for cycles, and the new DAG
proof-dependency edges were checked for a return path to this node. All three
original holes are closed and there are no `sorry` tokens in the module.

Updated the node's proof, proof dependencies, and proof origin. The two interface
change records are:

- `coord/changes/frobenius-point-finite-sigma-specification.md`
- `coord/changes/frobenius-point-integral-sigma-specification.md`

## Proved and sorry left

Closed three of the original three holes, all attached to
`def-weil-frobenius-point-transport`:

- `WeilConjectures.frobeniusPointFiniteSigma_existsUnique`
- `WeilConjectures.frobeniusPointIntegralSigma_existsUnique`
- `WeilConjectures.frobeniusPointTransportIntegral_existsUnique`

Retained holes in the item: zero. Added holes: zero. Split-off statements: zero.
The prime-unit theorems were already proved before this delivery and are not
counted as newly closed holes.

## No longer needed

No original import was removed, and no module or node is withdrawn or pruned.
The original node has no listed proof steps or proof dependencies to prune. The
common-refinement argument suggested by the old transport docstring is replaced
by the existing whole-tower counit characterization and adjunction uniqueness;
no additional common-refinement lemmas are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was found false. The original pointwise sigma
specifications caused excessive definitional reduction even before adding proofs;
the equivalent function formulation repairs that compile-cost problem. The proof
also fixes the coefficient presentation explicitly before applying sectionwise
naturality, avoiding repeated conversion between the completed ring limit and
its canonically identical presentation with commutativity retained. The
original node's proof field was empty; it now records the actual argument.

The two sigma specifications require no external adaptations:
`tools/downstream.py --uses` reports only this item for either theorem. Their
canonical choice definitions keep the same witness types and require no edit.
The proof treats unbounded complexes and all integer degrees. Its generic
sectionwise construction does not require a nonzero coefficient ring, and the
finite case includes exponent one (`n = 0`).

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
