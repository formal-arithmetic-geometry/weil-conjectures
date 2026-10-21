## What changed

Proved `SheafOfModules.coefficientSequenceSectionsLimitComparison`, with all four
normalization/projection clauses and its original signature. All six existing definitions
and instances are unchanged. Added proved private helpers for universal derived pairs,
tower Grothendieck categories, the split-transition Roos computation, restriction
identification, acyclicity, and the constant-coefficient comparison and projections.

The varying-ring acyclicity step uses the existing
`SequenceProjection.pushforwardLimitProjections` clause. Its restriction is identified
with the specified restriction using the actual level and transition equations. For
constant coefficients, the constant-tower adjunction and the split-transition Roos
calculation in abelian groups supply both composition computations. The final proof
retains the ordinary cone normalization and the supplied finite evaluation comparison.
The node and proof docstring record this route. No other module is changed.

The whole module compiled without warnings before import cleanup (43.1 seconds), and
again after removing the two unused ordinary proof imports (35.3 seconds). The final
public-import cleanup also passed the delivery compilation. That delivery attempt
pushed nothing: preflight requested a change record for public-import removals and
section commands. Added
`coord/changes/coefficient-sequence-sections-limit-proof-interface.md` with the
old/new imports and section prelude. The downstream consumer check reports zero
importers; only the item mentions the checked declarations. No adaptation is needed.

## Proved and sorry left

Closed 1 of 1 original holes:
`SheafOfModules.coefficientSequenceSectionsLimitComparison`
(node `lem-coef-sequence-sections-limit-comparison`).

Added 0 holes; split off 0 statements. Zero `sorry` tokens remain in the item. All private
helpers are proved. Existing imported declarations that still contain `sorry` are used
under the stage-3 dependency policy; no imported theorem is re-stated or weakened.

## No longer needed

Removed direct proof imports:
`Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses` and
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`.
Removed the unused public import `Sheaf.CategoryTheory.RingedToposMorphism`.
`Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients` is now
imported privately with `import all`, instead of both publicly and privately: the proof
uses its proved splitting/kernel helpers, while the public statements do not need it.

The old direct proof dependencies `def-pc-sheaf-restrict-scalars`,
`lem-pur-system-ringed-sequence-site`, and
`lem-weil-pbc-ringed-topoi-derived-pushforward-composition` are not invoked directly.
The sequence-projection theorem already supplies the varying-ring composition clause;
the constant-coefficient composition is proved by the split-transition Roos argument
and universal derived-functor uniqueness. These nodes remain needed transitively by
existing dependencies, and the statement dependencies are preserved. Their obsolete
direct tool-use entries are removed without changing other maintainer approvals.

No whole module is withdrawn or claimed to leave the target import closure. The
strict-tower homotopy-limit and tower-evaluation dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The planned mathematical argument is sound. Directly applying the generic ringed-topos
composition interface would require common small-site/coefficient universes, whereas
this statement allows an independent coefficient universe over an essentially small
site. The existing sequence-projection theorem has the required universe-general
acyclicity clause. Its DAG dependency closure and Lean import direction were checked
not to return to this item.

The original plan's second composition step can be replaced by the simpler
split-transition argument in abelian groups. It requires neither exact products of
module sheaves nor preservation of K-injectives by varying-ring restriction or
varying-ring evaluation. No statement, target definition, or blueprint unit route changes.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
