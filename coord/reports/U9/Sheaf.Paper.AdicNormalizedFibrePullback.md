## What changed

Replaced the only proof hole in `Sheaf.Paper.AdicNormalizedFibrePullback` by a
complete assembly from three strictly smaller intermediate statements. The original
`NormalizedPullback` structure and theorem signature are unchanged. No source-library
file, existing definition, target, public import, or consumer is changed.

`NormalizedPullbackObjects` states objectwise isomorphisms with the actual counit,
germ and integral chart equations, but no heart-arrow naturality and no identity or
composition coherence. `NormalizedPullbackNaturality` supplies the commuting square
for an already given objectwise package. `NatIso.ofComponents` constructs the natural
isomorphisms in the item. `NormalizedPullbackCoherence` supplies identity and
composition equations for those same components and the actual raw comparisons.
Both normalization clauses then transfer to the assembled natural isomorphism.

The item constructs the local inverse-limit isomorphism explicitly by
`HasLimit.isoOfNatIso` applied to `pullTowerIso`. Its finite projection equations are
`HasLimit.isoOfNatIso_hom_π`. The proved private `pullLimit_unique` identifies it with
the comparison in the objectwise package, using `limit.hom_ext`, `Iso.ext`, and proof
irrelevance; the item transports the local equation along this equality.

The original eight-step route is retained below the three new nodes. The new theorem
docstrings and nodes include complete proofs in words and the source references.
The three remaining obligations are a decomposition, not a completed proof of the
underlying geometric comparison. They cannot individually replace the original theorem:
the first lacks naturality and coherence, and the other two assume an objectwise family
and construct neither its fibres nor its local models.

## Proved and sorry left

Original holes: 1. Closed in the item:
`AlgebraicGeometry.Scheme.AdicFibreComparison.adic_normalized_fibre_pullback`.
Its proof is complete relative to the three named intermediate statements.
Also proved: private `pullLimit_unique`; the inverse-limit comparison and projection
formula are constructed directly from Mathlib in the main proof.

Added holes: 3, each a whole public theorem in its own new module:

- `AlgebraicGeometry.Scheme.AdicFibreComparison.objectwise_normalized_fibre_pullback`
  (`lem-per-normalized-pullback-objects`).
- `AlgebraicGeometry.Scheme.AdicFibreComparison.objectwise_normalized_pullback_naturality`
  (`lem-per-normalized-pullback-naturality`).
- `AlgebraicGeometry.Scheme.AdicFibreComparison.objectwise_normalized_pullback_coherence`
  (`lem-per-normalized-pullback-coherence`).

No other sorry is present in the delivered files. This is one upper hole decomposed
into three lower obligations, not a net hole reduction. No definition is constructed
from an arbitrary unproved existence witness; the only objectwise existence theorem
is eliminated inside the existential proof of the original theorem.

## No longer needed

Removed direct proof imports of `Sheaf.Paper.AdicNormalizedFibreExactness`,
`Sheaf.Paper.LisseCompletedSystemComparison`,
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`, and
`Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound` from the item. The item now
imports just its unchanged public data prerequisite and the three proof modules it uses.
These removals do not withdraw their nodes: all seven original proof dependencies
remain recorded below the objectwise/naturality/coherence obligations. The geometric
facts are already available in `base` at the assembly level. No module is withdrawn,
and no original dependency is claimed mathematically unnecessary.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was found. The existing declarations supply
normalized fibres, lisse systems, stalk germs, and raw realization coherence, but do
not yet state the gluing argument joining the local comparison data, heart-arrow
naturality, and normalized raw coherence. The new nodes isolate these missing steps.

Edge cases checked against the statements and source: an empty scheme admits no
geometric point, rank-zero comparisons are the unique maps, the identity and composite
maps retain the raw comparison direction, and an arbitrary non-flat morphism is
handled on finite-free charts. The fractional argument only cancels uniformizer powers
after rationalization and does not assume integral Hom modules torsion-free. Every
chosen affine open in the pulled chart remains universally quantified.

## New nodes

`lem-per-normalized-pullback-objects`: the objectwise portion of the original steps
1–4 and local-model identification of step 7, including all prescribed counit and
integral equations. Its module also declares `ObjectwiseNormalizedPullback` to spell
out these data. Source: Bhatt–Scholze 6.8.4(1),(4),(6), 6.8.15 and Stacks 03Q1(3).

`lem-per-normalized-pullback-naturality`: steps 5–7, restricted to the commuting square
for a heart arrow and a given normalized objectwise package. The argument uses a
fractional lattice representative on a pointed affine common refinement, then clears
denominators after rationalization.

`lem-per-normalized-pullback-coherence`: step 8, restricted to identity and composition
for a given normalized objectwise package. Its underlying heart isomorphisms must be
exactly the raw comparisons supplied by R.

LeanSearch, LeanFinder, Loogle and Mathlib/source grep found generic inverse-image,
point and free-pullback APIs, with no match for these normalized continuous adic
assertions. The logged queries and their actual results are recorded in the nodes.
The unit and chapter route are unchanged. No existing interface changes require a
change record or forced consumer adaptation.

## Second reading by U9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
