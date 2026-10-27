## What changed

Replaced the direct hole in `TopCat.Sheaf.spectralLimit_cohomology_class_lift`
by simultaneous induction over the degree and all compatible coefficient systems.
Degree zero uses compact-open preservation of the sheaf colimit, the existing
finite-stage unit generation theorem, and surjectivity of universal-generator
evaluation, proved here through the sheafification, free and Yoneda adjunctions.
The successor proof chooses a preimage under a surjective boundary, applies the
induction hypothesis to the quotient system, and uses the canonical boundary square.
The original theorem signature and public imports are unchanged.

Added `Sheaf.Topology.SpectralLimitAcyclicReplacement`, the remaining dimension
shifting construction: a compatible quotient system, stage and limit boundaries,
surjectivity of the limit boundary, and their compatibility with canonical maps.
Its proof in words constructs compatible injective embeddings and an acyclic middle
limit. It assumes no generation theorem. The parent degree-zero proof and induction
are complete Lean proofs from this strictly smaller construction step. Updated both
DAG records.

## Proved and sorry left

Original module: one direct hole before, zero after. The closed original declaration
is `TopCat.Sheaf.spectralLimit_cohomology_class_lift`. This is a decomposition, not a
net proof closure: one lower hole is added in
`TopCat.Sheaf.spectralLimit_acyclic_replacement`
(node `lem-weil-pbc-spectral-limit-acyclic-replacement`).

The private helper `eval₀_surjective` has a complete proof. Degree-zero generation
is written directly in the induction. The successor assembly uses surjectivity,
the induction hypothesis, and composition of equalities. No data definition, axiom
or private declaration contains a hole. Existence witnesses of the remaining theorem
are eliminated only inside a theorem proof; no definition chooses arbitrary data.

## No longer needed

The original module no longer directly imports:

- `Mathlib.Algebra.Category.Grp.AB`
- `Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf`
- `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`
- `Mathlib.CategoryTheory.Abelian.RightDerived`
- `Mathlib.CategoryTheory.Preadditive.Injective.Basic`
- `Mathlib.Topology.Sheaves.Functors`
- `Sheaf.CategoryTheory.SiteCoveringAxioms`
- `Sheaf.Topology.SpectralDirectedLimit`
- `Sheaf.Topology.SpectralLimitDescendOpens`
- `Sheaf.Topology.SpectralLimitSheafSections`
- `WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence`
- `WeilConjectures.CategoryTheory.SiteCechVanishingCriterion`
- `WeilConjectures.CategoryTheory.SiteCohomologyPullbackData`
- `WeilConjectures.Topology.Sheaves.Cech`
- `WeilConjectures.Topology.Sheaves.PushforwardCohomology`

The base case uses `lem-weil-pbc-abelian-large-compact-open-colimit` and
`lem-weil-pbc-spectral-limit-unit-generation` directly, instead of constructing the
full comparison diagram of `lem-weil-pbc-spectral-limit-sheaf-sections`.
The nodes `lem-weil-pbc-derived-functor-injective-vanishing` and
`lem-weil-pbc-derived-functor-long-exact` are no longer used by this argument:
positive acyclicity is proved directly by Cech comparison, and the boundary
surjectivity uses object-cohomology Ext exactness. The following dependencies move
from the parent to the replacement node; they remain needed there:

- `def-weil-pbc-sites-and-cohomology`
- `def-weil-pbc-topological-inverse-image`
- `def-weil-spectral-space`
- `lem-pc-topological-injective-cech-positive-exact`
- `lem-sc-topological-pushforward-injective`
- `lem-weil-pbc-filtered-colimit-abelian-groups-exact`
- `lem-weil-pbc-product-injectives`
- `lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact`
- `lem-weil-pbc-site-cech-vanishing-criterion`
- `lem-weil-pbc-site-sheaves-enough-injectives`
- `lem-weil-pbc-spectral-directed-limit-spectral`
- `lem-weil-pbc-spectral-limit-descend-opens`
- `lem-weil-pbc-spectral-limit-sheaf-sections`

Ext exactness is used in the replacement node's proof plan; the parent only uses
the resulting boundary interface.
No module is withdrawn and no global pruning claim is made. All adopted upstream
declarations are preserved.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The degree-zero step needed an explicit finite-stage
unit-generation argument after representing a colimit section; the previous
high-level description suppressed these transports. The compatible acyclic
replacement is substantial construction work not supplied by a theorem on full
topological open-set sites. The general colimit-sites injective system theorem
requires finite covering presieves and is not directly applicable here.
The replacement's proof in words derives the boundary square from normalized
pullback compatibility and extension-class naturality for the canonical stage-to-limit
short-complex morphism. Its surjectivity follows from positive acyclicity and the
existing Mathlib leaf `lem-sc-abelian-ext-covariant-exact`. It assumes no class lifting.
The unit route is preserved.

The earlier sandbox packet was retained and reconciled; no second copy of its
remaining obligation is delivered. The resumed session repaired the Ext exactness
call, universal-generator evaluation and boundary transports. The cohomology functor
is locally irreducible during the induction so elaboration uses its API instead of
expanding the derived-category construction. No global definition is changed.

## New nodes

`lem-weil-pbc-spectral-limit-acyclic-replacement` in
`dag/nodes/sec-proper-base-change/`: the compatible dimension-shifting construction,
with surjective limit boundary and its square with stage boundaries. The docstring
and node give compatible products of pushforwards of injectives, quotient universal
properties, finite compact cover descent, Cech comparison, exact-colimit acyclicity,
and Ext exactness, following Stacks Tag 0A37. This construction has no induction or
finite-stage class representation. Checked singleton indexing, the empty spectral
space, degree one, and empty compact covers; none requires an additional hypothesis.
Searches of Mathlib and the blueprint found no theorem with this conclusion.
No change record is needed because no existing statement or definition changes.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
