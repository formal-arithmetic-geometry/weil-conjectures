## What changed

Added two proof-dependency modules, `Sheaf.Paper.DiagonalClosureOrdinaryLineFactor` and
`Sheaf.Paper.DiagonalClosureOrdinaryLineFactorIso`, and imported the latter from the item.
The item now obtains a normalized factorization map, installs its invertibility instance,
and packages it as the requested module isomorphism.  The item signature is unchanged.

## Proved and sorry left

The item theorem `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalClosure_ordinaryLine`
now has a complete proof from the two named intermediate statements.  The factorization
statement is proved directly from the existing qbar action uniqueness theorem.  One strictly
smaller geometric statement remains as a named `sorry`:

- `diagonalClosure_ordinaryLine_factor_isIso` in
  `Sheaf.Paper.DiagonalClosureOrdinaryLineFactorIso` (node
  `lem-diagonal-closure-ordinary-line-factor-iso`), proving invertibility for a map already
  satisfying that equation.

No definition contains `sorry`.

## No longer needed

No existing imports or proof-dependency nodes are pruned.  The original coefficient-map
import remains the public statement import; the two new modules are private proof imports.
The parent proof no longer needs to treat the ordinary comparison as an undivided step: its
factorization and invertibility substeps are recorded by the two new nodes.

## Where the brief, the DAG or earlier work was wrong

The declared root-basis and coefficient-colimit dependencies do not expose a global
scalar-extension isomorphism theorem.  They provide only slice-level normalized basis maps
and the regular-module multiplication comparison.  The remaining geometric argument must
therefore be split into factorization and invertibility before the item can assemble its
`Iso`.  This delivery makes that decomposition explicit.

## New nodes

`lem-diagonal-closure-ordinary-line-factor` and
`lem-diagonal-closure-ordinary-line-factor-iso` are the two strictly smaller ordinary
comparison steps described above; each has a corresponding module and DAG record in the
sandbox.

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
