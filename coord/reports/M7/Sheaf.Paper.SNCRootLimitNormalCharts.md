## What changed

Proved `AlgebraicGeometry.ProEtale.sncRootLimit_normal_charts` with its original signature,
universes and public imports. Added only proved private helpers in the item module.

The proof uses the already stated finite SNC root regularity, regular-ring normality,
weakly étale normality ascent, filtered-colimit normality and flat root-tower transport.
The polynomial evaluations defining finite and full root maps are explicit. Their inverse,
factorization and uniqueness proofs identify finite base change with the tensor quotient
and the full presented root algebra with the canonical ring colimit. `AsSmall` reindexes
the countable divisibility category into the ring universe without restricting `u`, `v` or `w`.

For the boundary product, the proved upstream Cartier affine-generator theorem gives
injectivity immediately. Reducedness of its principal ideal descends to each factor by
cancellation. Repeated branch supports would make a factor a unit, contradicting the
nonempty irreducible-component hypothesis. This supplies the extra `hreduced` and
`hdistinct` arguments required by the finite-root dependency without adding hypotheses.
The DAG proof and dependencies now follow this argument. No definitions or public
interfaces were changed; no consumer adaptations or change records are needed.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.ProEtale.sncRootLimit_normal_charts`
(node `lem-sfb-snc-root-limit-normal-charts`).

Validation: the complete item compiled through `lcompile.py` in 25.5 seconds.
The final delivery runs the required fresh compile and declaration/axiom probes.

Added zero holes and split off zero statements. The item contains zero `sorry` occurrences;
every private helper has a complete proof or explicit construction. Existing dependency
holes remain in their owning modules, notably
`AlgebraicGeometry.isRegularRing_snc_finiteRoot`,
`RingHom.WeaklyEtale.isNormalRing`, and
`Algebra.flat_root_tower_nonzerodivisor`; this delivery does not modify them.

The proof treats arbitrary coefficient and target universes, zero rings and empty
boundaries uniformly. The theorem is proved from the existing declared dependencies;
this does not claim that the entire transitive closure is already sorry-free.

## No longer needed

The direct proof dependency `lem-sfb-snc-branch-equation-nonzerodivisor`
(`Sheaf.AlgebraicGeometry.SNCBranchEquationNonzerodivisor`) is unnecessary here:
Cartier regularity of the supplied product ideal already gives the needed injection.
No module is withdrawn or deleted.

Removed unused direct proof imports:
- `WeilConjectures.RingTheory.ProEtale.WeaklyEtaleIndEtale`
- `WeilConjectures.RingTheory.EtaleNormalRing`
- `Mathlib.RingTheory.AdjoinRoot`
- `Mathlib.Algebra.Category.Ring.FilteredColimits`
- `WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs`
- `Mathlib.RingTheory.LocalProperties.Basic`

The first two remain needed inside the separate weakly étale ascent theorem; this is
removal of redundant parent imports, not withdrawal of those source declarations.
Removed obsolete parent `tool_uses` entries for the ind-étale refinement, étale normality,
monic quotient freeness, elementwise filtered colimits, regular local domains, and
maximal-localization ideal membership. The ascent and flat-tower children retain whatever
they need. The existing unit and chapter routes remain unchanged. The additional existing Cartier
affine-generator theorem is used as a generic algebraic tool, not a replacement of a
unit-level six-functor argument; it is already proved in the source library.

## Where the brief, the DAG or earlier work was wrong

The module docstring describes the older nine-step proof, while the current DAG has already
factored weakly étale ascent and flat-tower transport into existing statements. The proof
uses those current interfaces. The finite-root theorem requires reduced individual branch
quotients and distinct supports, which the item does not assume separately; these are
proved from the reduced regular product ideal, rather than silently assumed.

The geometric codimension argument for nonzerodivisors is redundant once the hypothesis
`H.IsInvertible` and the supplied product-ideal equality are used. No false statement or
unit-route error was found. Searches used the required `msearch.py` LeanFinder, Loogle and
grep modes, together with repository and Mathlib searches. The existing source Cartier
lemma supplied the shorter injection route; no new nodes were introduced.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
