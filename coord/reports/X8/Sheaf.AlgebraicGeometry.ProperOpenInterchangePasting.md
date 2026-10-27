## What changed

Filled `AlgebraicGeometry.Etale.properOpenInterchangeHorizontalPasting_of_normalization`
without changing its signature. Reused the proved private `ordinary_horizontal` from
`Sheaf.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization` through a proof-only
`import all`. Combined the resulting ordinary equation with the existing proved
`Functor.rightDerivedFunctorPlusBaseChange_naturality` and
`Functor.rightDerivedFunctorPlusBaseChange_paste` from the source library. The final
calculation inserts and cancels exactly the compositors in the statement.
Updated the item's DAG proof to this existing-library route. No definitions or
other modules changed; no unit route changed.

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Etale.properOpenInterchangeHorizontalPasting_of_normalization`
(node `lem-cbc-normalized-proper-open-pasting`). Added 0 holes; split off 0 statements.
No sorry remains in the delivered Lean module. The completed proof compiled through `lcompile.py` in 4.6 seconds. The two
pre-existing unused binder-name warnings are suppressed locally without changing
the signature. Delivery runs the required server preflight.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ProperSupportSheafComposition`: the ordinary calculation is
already available in `EtaleProperOpenHorizontalNormalization`. Its proper-support
machinery remains a transitive dependency of that existing proof, so this delivery
does not claim that module or its nodes are globally pruned.
Also removed the redundant proof import
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, already
provided by the existing public imports.
The explicit finite-type proof step in the old DAG plan is unnecessary in the
new proof. `def-weil-finite-type-morphism` is no longer a direct proof dependency;
proper/open hypotheses keep their original meaning. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No incorrect statement found. The previous plan overlooked the now-proved ordinary
horizontal calculation (landed after the original split) and the source library's
bounded-below base-change naturality and pasting API. Those give a direct proof,
without constructing additional support comparisons or choosing resolutions here.

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
