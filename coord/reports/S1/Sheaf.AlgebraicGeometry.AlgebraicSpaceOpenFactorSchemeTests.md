## What changed

Filled the three proofs in
`Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenFactorSchemeTests` without changing
any declaration signature, definition, attribute, or public import. Added a proof
import of `AlgebraicSpacePointOpenCalculus` and Mathlib support for subcanonical
over-sites, sheaf limits, and type-valued pullback squares.

Private helpers construct the algebraic-space structure of the literal open
subfunctor, identify its preimage with the sheaf pullback, and transport point
images through that comparison. The sheaf/representability helper arguments were
adapted from the existing private proofs in `EtaleSchemeMapOpenImage`; the
preimage-square argument was adapted from `OpenCoverRepresentableDiagonal`.
Neither module is imported: their public results concern different statements,
and the former depends on this item through its open-image parent.

The factor is the inverse of the full preimage inclusion followed by
`Subfunctor.fromPreimage`. Cancellation of a monomorphism supplies both the
canonical comparison (with both projection identities) and the scheme-test
etaleness. The existing point calculus supplies full-image and surjectivity
criteria, including the arbitrary-base-change image formula.

Validation: the final remote single-file compile passed without warnings in
5.7 seconds. The delivery tool runs the required preflight and axiom probe.
Source read: Stacks `spaces-properties.tex`,
`lemma-points-cartesian`, `lemma-characterize-surjective`,
`lemma-factor-through-open-subspace`, and `lemma-etale-image-open`.
Empty opens, the full open, strict image containment, empty sources, and
arbitrary base-change maps are covered: no proof adds a nonemptiness,
etaleness, flatness, or surjectivity assumption on the base-change map.

## Proved and sorry left

Closed all three original holes, attached to
`lem-a1-space-open-factor-scheme-tests`:

- `AlgebraicGeometry.AlgebraicSpace.openSubspace_preimage_schemeTests`.
- `AlgebraicGeometry.AlgebraicSpace.openSubspace_factor_schemeTests`.
- `AlgebraicGeometry.AlgebraicSpace.openSubspace_pullback_image`.

No `sorry` remains in this module; none is added anywhere. No split-off
statements or new nodes. These proofs use the already stated
`AlgebraicGeometry.AlgebraicSpace.point_open_calculus`, whose existing proof
obligation remains with its own module.

## No longer needed

No public imports removed. The node no longer directly uses
`lem-trf-space-fibre-products-etale-covers` as a proof dependency, so its direct
proof edge and corresponding obsolete `tool_uses` entry are removed. Categorical
pullbacks of sheaves and their preservation by the inclusion into presheaves
supply the comparison objects directly. This is not a withdrawal or a claim
that the fibre-product module is globally unused: it remains a statement
dependency and is also reached through the point calculus.

No other nodes or modules are pruned, and every other stated proof dependency
is used. The blueprint unit's route and all its realizations are unchanged.

## Where the brief, the DAG or earlier work was wrong

The `OpenSubspace` definition records representable openness but does not export
the automatic algebraic-space structure mentioned in its node. Existing private
helpers already prove that bridge, so the delivery reconstructs it privately
without introducing a new definition, interface change, or mathematical hole.
No false statement or source error was found.

## Second reading by S1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
