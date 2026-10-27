## What changed

This is a partial delivery. The original topological-coefficient transfer theorem keeps its
signature and its one `sorry`. The finite discrete coefficient alternative is now proved on
arbitrary affine schemes, without Noetherianity, by
`AlgebraicGeometry.ProEtale.finiteCoefficient_serreHeart_cohomology_vanishes` in the item module.
The item privately imports the two assembly lemmas below. Its proof-status docstring records
this finite branch without claiming the remaining coefficient alternatives.

Four new modules contain proved supporting statements:

- `Sheaf.Paper.TorsionCdIndFiniteHeart`: combine the existing finite-heart bound at the identity
  pro-etale test with the proved filtered sections continuity theorem.
- `Sheaf.Paper.ConstructibleFiniteHeart`: realize every constructible module by its degree-zero
  single complex, including a construction of the zero module's finite scalar local model.
- `Sheaf.Paper.FiniteDiscreteSerreIndConstructible`: use exact etale comparison to obtain an
  etale antecedent of a module in the finite discrete weak Serre coproduct hull. Present that
  antecedent by constructible etale modules and transport the filtered cocone to internal modules.
- `Sheaf.Paper.FiniteCoefficientSerreIndHeart`: explicitly compare the lifted coefficient
  encodings, transport weak Serre hull membership and filtered cocones along restriction of
  scalars, and turn the constructible stages into finite complex hearts.

All imports used only in proofs are private. No existing definition or declaration signature,
source-library file, consumer, target, or unit route is changed. Empty schemes and the zero
coefficient ring are covered by the constructions, without a nontriviality assumption.

## Proved and sorry left

Original holes closed: **0 of 1**. Holes added: **0**. This is proved infrastructure and a proved
coefficient subcase, not a proof or a decomposition of the original theorem.

The sole remaining hole in the packet is
`AlgebraicGeometry.ProEtale.torsionCd_topological_serreHeart_cohomology_vanishes`
(node `lem-sfb-torsion-cd-topological-serre-transfer`). Its original named theorem and disputed
proof status remain in place.

The following five public declarations have complete Lean proofs:

- `AlgebraicGeometry.ProEtale.constructible_le_finiteConstructibleComplexHearts`;
- `AlgebraicGeometry.ProEtale.FiniteDiscreteOrdinary.finiteDiscrete_serre_is_indConstructible`;
- `AlgebraicGeometry.ProEtale.finiteCoefficient_serre_is_indFiniteHeart`;
- `AlgebraicGeometry.ProEtale.torsionCd_indFiniteHeart_cohomology_vanishes`;
- `AlgebraicGeometry.ProEtale.finiteCoefficient_serreHeart_cohomology_vanishes`.

These proofs use existing declared project dependencies, including the finite-heart
cohomological estimate. They do not claim that every transitive dependency is already free of
`sorry`. Every private helper added here is proved. No arbitrary object is selected from a new
unproved existence statement; the existing encoding theorem determines its equivalences up to
canonical isomorphism, and the constructible-colimit theorem is used propositionally to prove
existence of a presentation.

## No longer needed

No existing import, node, module, or maintainer tool approval is removed or pruned.
The repaired Noetherian filtered-heart approximation is unnecessary for the finite discrete
coefficient branch, which instead uses ordinary etale constructible presentations. It is not
claimed unnecessary for the unresolved original theorem or the existing Noetherian subcase.

An exploratory cohomological-bound closure helper and a former standalone finite-coefficient
corollary are excluded from the packet. The corollary now lives in the assigned item module.
Neither excluded file was part of the existing library, so this withdraws no library module.

## Where the brief, the DAG or earlier work was wrong

The old arbitrary-affine finite-heart approximation had already been refuted and repaired to
require Noetherianity before this session. Its Stone--Cech kernel counterexample invalidates
that structural approximation, not the stated cohomological vanishing. The parent theorem
still has no Noetherian hypothesis. I found no valid argument replacing that step for all
its topological coefficient alternatives, and do not claim a counterexample to its conclusion.
The inherited `STATEMENT-DISPUTED` annotation is retained.

For finite discrete coefficients this gap can be bypassed using the existing etale comparison
and filtered constructible presentation theorems. Thus this coefficient branch does not need
the invalid general approximation. The conditional ind-finite-heart bound is also proved for
all the coefficient alternatives exactly as stated in its existing finite-heart dependency.

## New nodes

`lem-sfb-constructible-finite-heart` records the proved single-complex realization in
`Sheaf.Paper.ConstructibleFiniteHeart`.

`lem-sfb-finite-discrete-serre-ind-constructible` records the proved normalized finite discrete
etale-comparison presentation in `Sheaf.Paper.FiniteDiscreteSerreIndConstructible`.

`lem-sfb-finite-coefficient-serre-ind-heart` records the proved coefficient-isomorphism and
universe transport in `Sheaf.Paper.FiniteCoefficientSerreIndHeart`.

`lem-sfb-torsion-cd-ind-finite-heart` records the proved conditional cohomological assembly in
`Sheaf.Paper.TorsionCdIndFiniteHeart`.

`lem-sfb-finite-coefficient-serre-cd` records the proved finite discrete coefficient branch in
the assigned item module. The original node adds this branch to its proof audit, while keeping
all the previously recorded dependencies and the explicitly unresolved step.

There are no statement-change records and no forced adaptations.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
