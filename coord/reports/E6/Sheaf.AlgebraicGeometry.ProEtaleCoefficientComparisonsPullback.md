## What changed

The integral clause `AlgebraicGeometry.ProEtale.sfb_integral_comparison_pullback`
now has a complete Lean proof from one separate finite-reduction mate lemma.
The proof obtains the normalized comparisons from `sfb_integral_coefficient_limit`,
constructs the ring-compatible pullback isomorphism inside `Mon`, proves every
projection equation by cancelling the pulled-back comparison, and transports the
limiting cone along a natural isomorphism of finite coefficient towers. Successor
naturality of that tower is proved from naturality of constant-sheaf comparisons;
`NatTrans.ofOpSequence` supplies naturality for every tower arrow. Forgetting ring
sheaves preserves the limit, checked after the limit-reflecting sheaf inclusion.

The finite mate calculation is stated in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback`, for one finite quotient,
arbitrary abelian sheaf maps, and a common continuous quotient map. It has neither
an integral comparison isomorphism nor a limit-preservation conclusion. Its source
is the finite-label and adjunction-mate calculation in Steps 1--2 of the parent
node and the second paragraph of the blueprint proof. The new statement was checked
on an identity base change, the empty base, the empty test object, a constant
quotient map, and the ordinary nonconstant reduction map. The universal natural
finite-label identifications exclude arbitrary permutations of the finite labels.

The two definitions `sfbConstantRingAbIso` and `sfbFiniteCoefficientPullbackIso`
are moved verbatim into that lower module and publicly re-exported by the item.
This prevents a circular import. Names, signatures, universes, visibility, and
bodies are unchanged. The change record is
`coord/changes/E6-finite-reduction-identifications-relocation.md`.
No consumer source is adapted. The existing localization and algebraic-closure
proofs are retained.

Further proof work establishes the constant-sheaf unit, finite-scalar transport, and
finite-representation base-change identities in a compiling scratch probe
(`scratchpad/FiniteTransportProbe.lean`, `oct20-finite-transport20.log`). The remaining
glue is the point-adjunction base-change unit and the final equality of mates. A
point-unit proof elaborates but encounters kernel reduction cost when its composite
functors are identified. These scratch probes are not part of the delivery and are
not counted as closed holes.

Verification: both sandbox modules compile through `lcompile.py --all`; the parent
proof has no `sorry`. Compiler-guided checks include the full projection and
limit-cone conclusions. A profiling check showed that retaining the small-site
properties import is needed for the sheafification instance search; it is retained.

## Proved and sorry left

One original hole is closed in the item:
`AlgebraicGeometry.ProEtale.sfb_integral_comparison_pullback`
(node `det-prop-sfb-qlbar-colimit-x-pullback`). The item has zero remaining holes.

One hole is added in a separate finite-level result:
`AlgebraicGeometry.ProEtale.sfb_finite_reduction_pullback`
(node `lem-sfb-finite-reduction-pullback`). Its proof is exactly `by sorry`, with the
source and complete proof in words in its docstring and node. No private helper
or definition contains a hole. This is a decomposition, one hole closed and one
added, with net hole closure zero; it is not claimed as a proof of the finite mate
calculation. Ring conjugation, diagram naturality, cancellation and limit-cone
transport are proved in Lean.

The localization and algebraic-closure clauses were already proved in the shared
baseline and are not counted as new closures in this delivery.

## No longer needed

The item no longer directly imports:

- `Sheaf.AlgebraicGeometry.ProEtalePointPullback` (already available through the
  integral-limit statement dependency).
- `Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage` (its role is in
  the new finite-level mate lemma, not the parent cone argument).
- `Sheaf.Topology.ProfiniteCondensedRing` (already in the public coefficient API).
- `WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization` (already
  publicly imported by `PadicIntegersInvertEll`).
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` (already in the public
  coefficient API).
- `WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.Defs` (already in the public
  constant-pullback API).

The generic representable inverse-image/Yoneda and finite-compositor calculation
of the old parent Steps 1--2 is confined to the new finite-level node. Those nodes
remain dependencies through that lemma; they are not claimed as globally pruned.
The parent directly retains the small-site properties import for instance search.
No blueprint unit statement or proof step is bypassed. No whole module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The integral-limit declaration supplies normalized comparisons and representability,
but not the compatibility of their finite projections under a change of base. The
remaining mate calculation therefore is a separate result, not an immediate
application of the integral-limit theorem or of preservation of colimits. Its
statement does not assume the integral comparison square or the desired preservation
of the infinite limit.

Earlier interrupted attempts and compile-service transport failures are recorded in
`scratchpad/findings.md`; none was treated as a delivered proof. The present service
has compiled the reduction. The resumed launcher reference clock is
2026-10-19 18:22:31 UTC (`.budget.start` 1792434151.215593); previous provider-interrupted
turns had already done proof and search work. No clock metadata was edited.

## New nodes

`lem-sfb-finite-reduction-pullback` is the single finite-level mate lemma in
`Sheaf.AlgebraicGeometry.ProEtaleFiniteReductionPullback`. It isolates the finite
constant identification and the point-adjunction compositor check of the parent
proof, independently of the completed integral limit. Its natural-language proof
uses the same representing-scheme route as the blueprint. The two unchanged
constant-sheaf definition helpers are attached to this new module in its Lean record.
The parent node now records the actual ring conjugation, finite-projection and
limit-cone proof. See the relocation change record named above.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
