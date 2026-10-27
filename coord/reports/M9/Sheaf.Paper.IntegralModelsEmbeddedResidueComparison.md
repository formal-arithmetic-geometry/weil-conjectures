## What changed

Replaced the single hole in `AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueComparison`
by an assembly using the existing essential-image criterion
`AlgebraicGeometry.Scheme.finiteRing_constructibleDerived_origin` and two independent steps.
The parent derives finiteness, discreteness and a field structure for the actual first quotient,
applies the finite-field criterion, and transports essential-image membership along the
first-reduction isomorphism in both directions. The original signature is unchanged. All four modules compiled together without errors or warnings through lcompile.py --all.
A previous delivery attempt timed out before pushing. Explicit typed reduction and
realization composites now keep the intermediate scalar constructions folded; the revised
full compile passed.

`Sheaf.Paper.EmbeddedFiniteCoefficientRealization` gives a concrete scalar map and functor:
constant functions on the point, pullback, derived extension, and the existing intrinsic
realization. Its data are actual composites and do not depend on a new existence theorem.
The same module defines the two actual reduction functors and their realized composites with explicit types and
irreducible bodies; neither contains any proof hole. The two new theorem modules separate the derived scalar square from the finite-field
cohomology/Tor argument. Both statements apply to arbitrary unbounded complexes. No definition
or statement in the existing library is changed; no consumer adaptations are necessary.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.integralModelsEmbeddedResidueComparison`
(node `lem-sfb-embedded-integral-residue-comparison`) by a complete assembly.
This is a decomposition, not a completed proof of the whole mathematical obligation.
Original holes: 1; original holes remaining: 0; new holes: 2; net holes closed: -1.

New named holes:

- `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.firstReductionComparison`
  (`lem-sfb-embedded-first-reduction-comparison`): only an isomorphism of the two realized
  derived reductions; it states no constructibility, Tor bound or etale-origin condition.
- `AlgebraicGeometry.ProEtale.IntegralModelsEmbedded.finiteFieldCohomologyCriterion`
  (`lem-sfb-embedded-finite-field-cohomology-criterion`): identifies constructibility and Tor
  bounds under a fixed realization for an arbitrary finite field complex; no integral
  extension, reduction square or etale-origin assertion occurs.

The realization module has zero holes. The concrete realization and both split theorem
statements have compiled together through the remote compile service. The reduction functors
have explicit source and target categories and are locally kept folded to bound elaboration;
the parent unfolds their equations once. The scalar-square statement uses the typed
realization composites, whose concrete bodies are the displayed original constructions. All diagnostic options were removed. Each remaining proof is exactly `by sorry`, public,
with a source and complete proof in words in its docstring and matching node.

## No longer needed

Removed the parent's direct proof imports:

- `Sheaf.AlgebraicGeometry.ConstantFieldTorBounds`: used in the written proof plan for the
  independent finite-field step, not by the assembly; its node remains needed there.
  The split statement itself needs no proof import of it.
- `Sheaf.Paper.FlatCommonQuotientReductionTower`: used in the written proof plan for the
  independent scalar-square step, not by the assembly; its node remains needed there.
  The split statement itself needs no proof import of it.
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`: its general coefficient-model
  equivalence is replaced here by the existing specialized, normalized finite-ring
  essential-image theorem. The parent no longer needs node `sk-thm-pe-constructible-comparison`.

The original dependency nodes `det-prop-integral-criterion-constant-coefficients` and
`det-prop-sfb-qlbar-colimit-x-integral-limit` are needed by the scalar-square step, not by the
assembly. `def-sfb-integral-model-generator-data` remains needed by the concrete realization.
No module is withdrawn or claimed globally unnecessary: other consumers can still need all
these modules, including transitive imports through the public embedded presentation.

## Where the brief, the DAG or earlier work was wrong

The original plan's generic statements use coefficient-sized small ringed sites; the assigned
statement uses actual embedded Type-0 coefficients and internal abelian module objects.
The two named transport steps make this additional work explicit. This does not dispute the
mathematical statement or alter the unit route. The existing finite-ring origin theorem is
a shorter final step than constructing another comparison equivalence from the generic
constructibleComparison theorem.

Edge cases checked in the mathematical statements: arbitrary unbounded inputs have no
boundedness assumed; zero complexes have interval [0,0]; the uniformizer hypothesis makes
the actual residue quotient a nonzero field; empty schemes and zero module objects impose
no extra hypotheses. Neither new statement is the assigned theorem under another name.

## New nodes

`def-sfb-embedded-finite-coefficient-realization` records the concrete scalar map, its ring-map
instances, and the composite realization functor in `EmbeddedFiniteCoefficientRealization`.

`lem-sfb-embedded-first-reduction-comparison` records the normalized derived scalar square in
`EmbeddedFirstReductionComparison`, sourced from the first paragraph and Stacks 099L/06YQ.

`lem-sfb-embedded-finite-field-cohomology-criterion` records the constructibility and Tor
transport step in `EmbeddedFiniteFieldCohomologyCriterion`, sourced from the first paragraph,
Stacks 03ET/00YV/06YQ and the existing constant-field Tor theorem.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
