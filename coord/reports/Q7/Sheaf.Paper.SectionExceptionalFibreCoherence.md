## What changed

Filled the five original theorem bodies in
`Sheaf.Paper.SectionExceptionalFibreCoherence`, preserving all 19 existing public declarations,
the geometric records, the specified comparison maps, and the unit route. Transitivity uses
compact-support exchange pasting, mates, pullback-unit coherence, and explicit section
pullback associativity. The base-change fibre squares follow by comparing the two
factorizations of their outer rectangle. Normalized comparison and specialization follow
from the fibre squares, naturality of the section-unit comparison, and the given uniqueness.

For etale families, the proof derives structural locality/base-change naturality by a complete
categorical counit and mate calculation. It then cancels a structural pullback square to
identify the fibre etale square and proves the section comparison coherence explicitly.
The one input not furnished by an existing declaration is stated separately in
`Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange`: compatibility of the
left-adjoint etale composition comparison with inverse exchange. This statement concerns
compact support and sum extension only, before taking mates, evaluating at coefficients,
or pulling back by sections. It is a proper part of Steps 4–6, not the original assertion
under a new name.

Added private proof helpers for these categorical calculations and natural inverse-image
coherence. The private natural locality isomorphism uses the existing uniquely characterized
counit-normalized choice. No data is chosen from a mere existence theorem. Added proof imports
for the etale comparison lemma, affine-linear exchange pasting, smooth exceptional base
change, and generic mate composition. Updated the original node's proof route and recorded
the new lemma's node, source, searches, and complete proof in words.

## Proved and sorry left

Original holes closed (5):

- `AlgebraicGeometry.Etale.sectionExceptional_fibre_coherence`.
- `AlgebraicGeometry.Etale.sectionExceptional_comparison_comp`.
- `AlgebraicGeometry.Etale.sectionExceptional_etale_fibre_coherence`.
- `AlgebraicGeometry.Etale.sectionExceptional_normalized_baseChange`.
- `AlgebraicGeometry.Etale.sectionExceptional_normalized_etale`.

The item module contains zero `sorry`. One hole is added in the separate module:
`AlgebraicGeometry.Etale.etaleAmbientLeftComparison_baseChange`, node
`lem-amb-etale-left-comparison-base-change`. Thus the packet closes five original holes and
adds one, for a local hole decrease of four. The target-closure ledger is computed by delivery. The etale coherence argument is a decomposition through
the new left-adjoint compatibility lemma; it is not counted as an independent completed
proof of that compatibility. The other four original proofs add no holes. Every retained private helper is proved. The normalization-refinement calculation was also
tested and proved while investigating the lower lemma; it is kept in scratch notes because
the remaining public statement still has a hole and does not use that helper yet.

Validation: the generic counit/mate helpers compiled independently. All 19 existing public
signatures and every existing non-theorem body were compared with the repository source and
match. Both node dependency unions and the new recorded Lean signature were checked. Both delivery modules compiled in import order without warnings (9.1 s and 37.6 s).
Delivery preflight is the remaining validation step.

## No longer needed

Removed these direct proof imports from the item module:

- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`.
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`.
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules`.

The retained original proof does not separately need
`lem-sbc-smooth-relative-dimension-permanence` or
`lem-weil-pbc-finite-type-over-noetherian`: each section pair already supplies its own
smoothness and Noetherian hypotheses. The explicit finite-twist pullback construction is
not used by any of the comparison equations. Compact-support composition, etale
sum-extension exchange, and evaluation compatibility remain needed below the new lemma;
they are not globally withdrawn. The corresponding direct tool uses were removed from the
original node, while the new node records the dependencies it needs. No module is withdrawn
and no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The geometric plan is consistent. Its etale Steps 4–6 need an equation combining the
specified graph-normalized etale left comparison, compact-support exchange, and the
inverse mate of the canonical pullback square. Existing declarations give its ingredients,
but no declaration states this equation. The packet isolates that missing left-adjoint
compatibility as a new sourced lemma, and supplies the remaining counit, unit, section,
and normalization glue in Lean. There are no statement or definition repairs, and no
forced adaptations.

The new statement was checked on identity maps, empty schemes, and zero coefficients;
its maps remain defined and the asserted equality is the usual composition/mate
compatibility. Neither smoothness nor a section is needed for this lower lemma.

## New nodes

`lem-amb-etale-left-comparison-base-change` in
`dag/nodes/sec-trace-formula/lem-amb-etale-left-comparison-base-change.json` realizes
`AlgebraicGeometry.Etale.etaleAmbientLeftComparison_baseChange` in the new module
`Sheaf.AlgebraicGeometry.EtaleAmbientLeftComparisonBaseChange`. Its source is Stacks
0F7J/0F7L and 03S6; its proof describes compact-support composition/base-change,
graph normalization, and the sum-evaluation transpose calculation. It is strictly below
the etale structural mate calculation and section pullback, which are proved in the item.
There is no change record because no existing statement or definition was changed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
