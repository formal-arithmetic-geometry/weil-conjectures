## What changed

Proved `WeilConjectures.IntegralSystemRealization.integralSystemOpenEvaluation_isIso`
without changing its statement or the public imports. The proof uses
`ordinaryOpenFiniteEvaluation`, including its actual counit normalization, and
`exact_localization_inverse_mate`. Private helpers identify the ordinary inverse
mate by the adjunction Hom equivalence, transport its finite adjunction by
left-adjoint uniqueness, and identify the resulting localized comparison with the
fixed `pullbackTensorDerivedEvaluation` using its cochain normalization and
uniqueness. Private helpers cache the existing exactness instances. Proof imports supply
the ordinary evaluation theorem, exact localization, and its factorization identity. Updated only this module's DAG proof, proof dependencies and proof origin.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.integralSystemOpenEvaluation_isIso`
(node `lem-sf-integral-system-open-evaluation`). No holes added or split off.
No `sorry` remains in the delivered module. Every new helper is private and proved.

## No longer needed

No existing import was removed: the public import of `IntegralSystemOperations`
is preserved. The former direct proof dependencies
`lem-coef-semilinear-derived-sections` (`Sheaf.Paper.SemilinearDerivedSections`)
and `lem-sf-open-tensor-normalization` (`Sheaf.SixFunctors.OpenTensorNormalization`)
are unnecessary as construction theorems for this proof: the existing ordinary
finite-evaluation theorem already provides the normalized ordinary comparison,
and exact localization handles the derived step. They are removed from this
node's proof dependencies. Their infrastructure can still occur transitively;
this delivery does not withdraw either module or claim global unreachability.
No new slice or sequence-site construction lemma is needed.

## Where the brief, the DAG or earlier work was wrong

The planned reconstruction of ordinary extension by zero is unnecessary here:
`ordinaryOpenFiniteEvaluation` already states the needed ordinary counit equation.
Combining that equation with injectivity of the finite adjunction Hom equivalence
identifies the specified inverse mate. The derived comparison cannot merely be
chosen arbitrarily; its prescribed cochain normalization is checked explicitly.
The statement, empty-open case, unbounded categories, and unit route are preserved.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
