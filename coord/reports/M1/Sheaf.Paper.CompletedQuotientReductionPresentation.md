## What changed

Proved `WeilConjectures.CompletedQuotient.completedQuotientReductionPresentation`
for the existing ordinary quotient complex and the prescribed coherent and finite
model isomorphisms. The theorem signature and all definitions are unchanged.
The proof identifies ordinary evaluation by uniqueness of adjoints, transfers the
ordinary quotient transition equation, computes total-limit projections using a
K-injective replacement, and compares the finite and coherent adjunction units.
All auxiliary statements are proved private lemmas in the item module.
Validation: `lcompile.py` compiled the final module successfully in 53.0 seconds
with no warnings, under the existing 60-second file limit.

Added proof imports of `Sheaf.Paper.PurSequenceOrdinaryFactorization`,
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`, and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback`.
The latter two supply localization-factor transport and the cochain right-derived
unit API. Updated the item's proof steps and dependencies to match the proof.

The ordinary factorization theorem is a tool from `sk-thm-sf-compatibility`:
it gives the exact ordinary transpose and quotient-transition equations already
used to define the fixed evaluation comparison in CompletedPullbackTowerCore.
The item's unit `sk-def-purity-conv` has no realized statement or proof steps;
no unit route is bypassed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.CompletedQuotient.completedQuotientReductionPresentation`
(node `lem-pur-completed-quotient-reduction-presentation`).
Added 0 holes; split off 0 statements. No `sorry` remains in the item module.
This proof uses the existing normalized model and adjunction declarations;
their independent proof obligations are unchanged.

## No longer needed

No existing import or module is removed. The direct proof dependency
`lem-pur-derived-change-of-rings` is replaced by the already normalized finite
scalar-extension/restriction adjunction
`lem-weil-derived-scalar-extension-restriction-adjunction`.
No additional application of general change of rings or fresh K-flat resolution
of the input is needed. The former dependency remains needed transitively by
other modules, so this delivery withdraws no module or declaration.

## Where the brief, the DAG or earlier work was wrong

The stated argument is valid. The DAG omitted the explicit ordinary factorization
API needed to transfer the quotient-transition identity and the finite derived
adjunction unit normalization needed to identify the canonical finite model.
These existing declarations suffice; no new intermediate obligations are needed.
The private exact-square and finite-unit calculations follow the proved helpers
in `Sheaf.Paper.CompletionUnitFiniteMateComparison`; the local versions are
specialized to this fixed quotient comparison, whose source is only the good
complex subcategory, rather than an arbitrary comparison on every complex.
The factorization exists for arbitrary schemes, so the proof adds no finite-type,
field-of-definition or boundedness hypothesis.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompletedQuotientReductionPresentation": "b8303885b4ce0d71564cf97452d408ca031eec8e"}, "results": {"Sheaf.Paper.CompletedComparisonQuotientNormalization": {"hash": "f19d20d87135ee7a4c197048bcde6400b92c1166", "status": "OK"}}, "seconds": 249, "time": "2026-10-28T00:05:42+0800", "transitive": 0, "version": 1}
```

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
