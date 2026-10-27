## What changed

Proved `WeilConjectures.coherentQuotientReductionComparison` without changing its
statement. The proof imports `CompletionUnitCanonicalModels` and
`CompletionUnitFiniteMateComparison` and `CoherentQuotientModelComparison`
privately. It transports the canonical model
from its chosen calculus to the supplied calculus, reconstructs the strict
comparison from the coherent tensor-unit map by ordinary adjunction, and compares
the derived maps using two injective adjunction Hom equivalences.

Two new proved modules expose `coherentQuotientOrdinaryLift` and
`coherentQuotientModelComparison`. Their private helpers prove the section-cast
identity, ordinary unit projection, equality of termwise limit comparisons,
normalized derived constant-tower counit and transpose formula, and detection
of strict complex isomorphisms by finite evaluations. Local irreducibility attributes keep large constructions folded during
elaboration inside these files. The node's proof and dependencies follow
this argument.

## Proved and sorry left

Closed: `WeilConjectures.coherentQuotientReductionComparison`
(`lem-trf-coherent-quotient-reduction-comparison`), the item's one original hole.
Added holes: none. Remaining holes in this delivery: none.
Also proved `WeilConjectures.coherentQuotientOrdinaryLift` and
`WeilConjectures.coherentQuotientModelComparison`; neither is a split-off obligation.

The proof uses existing stated dependencies, including
`WeilConjectures.CompletionUnit.finiteComparison_of_unit`; their unproved bodies
are existing project obligations, not new split statements in this delivery.

## No longer needed

No existing imports, modules, or nodes are withdrawn. The separate horizontal
assembly subargument of the old plan is unnecessary: coherence already supplies
a strict tower map, and two ordinary adjunctions turn it into the required chain
map. Neither the finite derived comparison nor the horizontal component of
`CoefficientReductionPresentation` is needed in this argument. Its hypothesis is
preserved unchanged. No equality of derived morphisms is inferred from finite
evaluations: those evaluations only detect the strict chain isomorphism.

## Where the brief, the DAG or earlier work was wrong

The canonical-model theorem chooses its own calculus, whereas this statement fixes
an arbitrary supplied calculus. The proof fills that glue explicitly by the unique
comparison of left adjoints and the existing finite unit-mate theorem. A coherence
witness for the supplied calculus is not assumed or manufactured.

Read the current blueprint trace-transport unit and the source ordinary and
derived adjunction and tower-limit arguments (Stacks 03D7, 07A6 and 0941). The
unit's route is preserved. The construction works for zero complexes and for
index zero (exponent one), and needs no boundedness or completeness assumption.

## New nodes

`lem-trf-coherent-quotient-ordinary-lift` records ordinary reconstruction from a
strict tower map with the prescribed generator values. The theorem constructs a
strict isomorphism and proves its ordinary transpose and finite comparisons.
It is fully proved in `Sheaf.Paper.CoherentQuotientOrdinaryLift`.

`lem-trf-coherent-quotient-model-comparison` records the derived comparison for
supplied normalized models M and D. It combines ordinary reconstruction with the
normalized constant-tower counit and two adjunction Hom bijections. It is fully
proved in `Sheaf.Paper.CoherentQuotientModelComparison`.

The self-contained parts were separated after profiling the complete file,
replacing dependent case splitting and repeated section/adjunction conversions
with explicit projection formulas and generic proved identities. There are no
changes to shared definitions and no change records or consumer adaptations.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
