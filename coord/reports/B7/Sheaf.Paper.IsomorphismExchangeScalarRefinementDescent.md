## What changed

Only Sheaf.Paper.IsomorphismExchangeScalarRefinementDescent and its existing DAG node.
Five component declarations now have complete Lean proofs from existing library declarations.
The rational identity/horizontal/vertical coherence clauses specialize LiftedCbc's
finite-extension theorems. Integral refinement, compactification independence and tower
refinement specialize the completed compact-support theorems. The two finite comparison
statements specialize the source library's compact-support formalism. Rational refinement
images follow by congruence from the integral refinement equation and the specified functors.
A proved private helper derives the field-base Noetherian, dimension and prime-unit domain.
Its dimension argument uses the existing proved private finite-type dimension bound via a
private `import all`. All original public imports and signatures are preserved. No definitions
or source-library files change. The main declaration is placed after the components.

The final file is compiled through lcompile.py; deliver3.py performs the delivery checks.
The discarded rational-normalization experiment is not part of the delivery.

## Proved and sorry left

Five of eight original holes closed:

- WeilConjectures.isomorphismExchangeLocalizedPasting
- WeilConjectures.isomorphismExchangeIntegralRefinement
- WeilConjectures.isomorphismExchangeFiniteCompactification
- WeilConjectures.isomorphismExchangeRefinementScalarImages
- WeilConjectures.isomorphismExchangeFiniteCommonRefinement

Three original holes remain, each attached to
lem-pur-isomorphism-exchange-scalar-refinement-descent and retaining its source and
complete proof plan in its docstring:

- WeilConjectures.isomorphismExchangeScalarRefinementDescent
- WeilConjectures.isomorphismExchangeScalarComparison
- WeilConjectures.isomorphismExchangeCommonStage

Zero holes added, zero split-off statements. This is a partial proof delivery, not a
claim that the three remaining declarations or their upstream dependencies are axiom-free.
The proved component declarations use already stated results, some of which remain sorry.

## No longer needed

Removed private imports from this module:

- Sheaf.CategoryTheory.SemilinearScalarLocalization
- Sheaf.Paper.RefinementExchangeCoherence
- Sheaf.Paper.RefinementComparisonIsomorphism
- Sheaf.AlgebraicGeometry.ProperOpenInterchangeCoherence
- Sheaf.Paper.StrictReductionCompactSupportNormalization
- Sheaf.Paper.CompletedRlimFunctor
- Sheaf.Paper.ConstantCompletionEquivalence
- Sheaf.Paper.CompleteProetaleStrictTowerRealization

The five completed proofs do not directly need the old strict-reconstruction route:
lem-cbc-complete-proetale-refinement-exchange-coherence,
def-sf-refinement-comparison-isomorphism, lem-cbc-proper-open-interchange-coherence,
lem-pur-strict-reduction-compact-support-normalization,
prop-weil-pbc-rlim-functoriality, lem-weil-pbc-constant-completion-equivalence,
lem-cbc-complete-proetale-strict-tower-realization and
lem-cbc-complete-proetale-composition-pasting-coherence.
They use thm-cbc-complete-proetale and fix-lem-exchanges directly instead.
The scalar-localization node remains in the planned argument of the unfinished main
normalization clause. Public strict-tower imports remain verbatim because their removal
would change the public API. No module is withdrawn or asserted globally unreachable;
lower results may remain necessary through the existing APIs or other consumers.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was found. The original plan repeats coherence
already present in the completed compact-support and finite-extension interfaces.
At finite coefficients the compact-support formalism already proves exactly both
comparison equations, so the longer tower calculation is unnecessary here.
The explicit refinement-image statement's last two conjuncts are functor images of
its first equality, as the earlier review observed. Edge cases such as identity
refinement, zero objects, equal compactifications and non-k-linear isomorphisms remain
covered by the same general library theorems. The unit route is unchanged.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
