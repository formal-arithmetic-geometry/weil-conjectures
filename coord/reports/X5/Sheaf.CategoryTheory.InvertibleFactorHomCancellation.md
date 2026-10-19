## What changed

Proved `CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation` in
`Sheaf.CategoryTheory.InvertibleFactorHomCancellation`, retaining its complete signature and
both canonical maps. Private proved helpers express the closed adjunction with evaluation on
the right, establish the evaluation equations, prove simultaneous cancellation using the full
faithfulness of tensoring with an invertible factor, and verify variable and factor naturality.
The first comparison reuses the library's proved `isIso_ihomTensorToIhom`. The inverse evaluation
and naturality equations follow by composition with the inverse isomorphisms.

Updated the node's proof and proof origin to record this reuse and the implemented Hom-set
argument. No definitions or statement signatures changed.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.MonoidalClosed.invertibleFactorHomCancellation`
(node `lem-sf-invertible-factor-hom-cancellation`). No holes added, no statements split off,
and no `sorry` remains in the delivery.

## No longer needed

Removed the redundant proof import `Mathlib.CategoryTheory.Equivalence`; the public rigid
category import already provides it. No dependency nodes or modules are pruned: the monoidal
category and quasi-inverse Hom bijection dependencies are used, the latter through
`tensorRightEquivalenceOfTensorIso` and its fully faithful functor. The duplicate implementation
of the first map's isomorphism test (original proof steps 4–5) is unnecessary because the
library already proves precisely that comparison invertible. No unit statement or step is
bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The assigned plan can be fully proved with the existing
library and Mathlib. Searches through leanfinder, loogle, the logged grep tool, and direct
source searches located the relevant ingredients; no Mathlib declaration directly provides
the entire evaluation-normalized conclusion. Read Stacks `categories.tex`,
`lemma-invertible` and `remark-internal-hom-monoidal`, and the library proof of
`isIso_ihomTensorToIhom`.

The preflight classifies the scoped `omit` commands on two private helpers as a
command/interface change. Their scope and the unchanged public interface are documented
in `coord/changes/invertible-factor-hom-cancellation-private-helpers.md`, including
all transitive importers; no consumer adaptation is needed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
