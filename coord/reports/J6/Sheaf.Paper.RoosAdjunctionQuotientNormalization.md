## What changed

Proved `WeilConjectures.roosAdjunctionQuotientNormalization` without changing its
statement, public imports, or any definition. All edits are in the assigned module
and its node `lem-trf-roos-adjunction-quotient-normalization`.

The proof takes the same S, coherence, M and D from
`CompletionUnit.completionUnitStrictQuotientModel`. It derives invertibility of
D.limitUnit and the Roos inclusion from their normalization. Private proved helpers
calculate the specified projections, extend the Roos projection formula from
K-injectives to all complexes, and apply `derived_tower_counit_projections` to the
canonical right-derived limit unit. Naturality then gives the resolution formulas
for the comparison, every projection, and the entire constant-tower counit. The
coefficient-system counit is exactly S.counit_projection; the quotient-model
section, coordinate, and whole-unit formulas are retained verbatim. H is the fixed
limit functor, κ is D.roos, and ρ is the identity.

The canonical adjunction and comparison-naturality helpers are generic in the abelian
category. This keeps kernel conversion of the complex-limit models manageable when
specialized to coefficient sheaves; the complete file compiled in 51 seconds.

The proof docstring and node proof/proof_deps/proof_origin now describe that argument.
The source read was Stacks sites-cohomology.tex, lemma-derived-limit-is-ok (0941),
with the node's whole-system adjunction and quotient normalization refinement.
The current blueprint unit and its realized record were read; no unit statement or
route is bypassed.

## Proved and sorry left

Closed one of one original holes:
`WeilConjectures.roosAdjunctionQuotientNormalization`
(node `lem-trf-roos-adjunction-quotient-normalization`).

No sorry remains in the item. No holes, modules, axioms, definitions, or public
statements were added. All seven private helper theorems have complete proof bodies.
This is a proof from existing declarations, including the existing canonical-model
dependency of the quotient-model theorem; it does not claim those dependencies are
axiom-free already.

## No longer needed

Removed these proof imports:

- `Sheaf.CategoryTheory.StrictRoosComparison`:
  `lem-weil-strict-roos-comparison` need not be applied again, since the compatible
  D already supplies its normalized comparison.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `lem-weil-pbc-ringed-strict-tower-homotopy-limit` need not construct a second
  derived-limit model; the fixed coefficient inverse limit and D suffice.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `lem-weil-proetale-countable-products-exact` is not used directly. The normalized
  compatible model already supplies the comparison needed here.
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`: available through the
  required derived-tower adjunction import.

Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`
for the canonical complex-level unit API. The derived-tower counit theorem and
completion-unit strict quotient theorem remain direct dependencies. The DAG retains
the K-injective homotopy-equivalence dependency and records the model and projection
APIs actually used. The three obsolete tool_uses approvals for the first three removed imports are
removed in their existing order. No declaration or module is withdrawn; these pruning claims
concern this proof's dependencies, not unrelated library consumers.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface repair was needed. The old plan redundantly rebuilt
the Roos and total-limit models before choosing a compatible quotient model. Taking
the quotient model first makes the comparison and unit use the same D by construction.
The whole-tower counit is obtained from the derived adjunction and naturality, never
by claiming finite evaluations determine arbitrary derived tower morphisms.

The proof adds no hypotheses. The zero complex, empty site, n=0 (positive quotient
exponent one), repeated coefficient fields, independent site/coefficient universes,
and unbounded complexes require no exceptional choices or divisions in this argument.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
