## What changed

Restored the assigned quarantined module
`Sheaf.AlgebraicGeometry.CoefficientConstructibleEtaleModules`, preserving all nine
public declarations and the existing complete continuity proof. Its assigned repair is
`coord/rework.tsv`'s unknown `LocallyClosedStratification` at line 111.

`Scheme.IsCoefficientConstructibleEtaleModule` now uses the current dependency-node
interface `Scheme.FiniteLocallyClosedStratification`, with a public import of
`Sheaf.AlgebraicGeometry.FiniteLocallyClosedStratification`. Its explicit constructibility
conjunct, finite strata, realizing schemes, immersions, affine-local quantifier and
finitely generated constant module models are retained. The bounded predicate and both
full subcategories retain their meanings and all ambient morphisms.

The existing node `def-pe-etale-constructible-module` keeps its Lean attachment, signature,
declaration list, statement dependencies, proof dependencies and unit. Only its Lean note
records the repair. Change record:
`coord/changes/C1-coefficient-constructible-stratification-restoration.md`.

Sources read: Stacks etale-cohomology.tex, definition-constructible, clause (3), Tag 03RW;
proetale.tex, lemma-compare-constructible-derived, Tag 09AL; the current unit blueprint.
Read the full recorded `FiniteLocallyClosedStratification` structure and the old upstream
`Scheme.Stratification` interface. The former is the exact recorded dependency, without
an implicit extra constructibility condition; this consumer supplies that condition itself.

Validation: remote lcompile of the restored item succeeds without diagnostics (2.5 s;
3.2 s when compiled together with the consumer). An unchanged copy of the archived
`Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback` compiles against it in 4.3 s.
The consumer check is scratch work and is not delivered. tools/downstream.py with
--allow-missing reports zero live downstream modules and zero live uses of the four
constructible predicates/categories. The five archived consumers are listed and inspected
in the change record; their independent missing dependencies/retired names remain separate
quarantine repairs. No live consumer requires adaptation.

Searched the library and used the existing recorded definition; msearch grep and Loogle
found no Mathlib stratification interface, while LeanFinder returned general scheme
properties rather than this finite immersed partition. No new interface was invented.
Edge cases checked from the real structures: empty scheme/n = 0, zero coefficients,
zero module, infinitely many elements in a finitely generated module, and non-quasi-compact
schemes where the stratification is allowed to depend on the affine open. Integer
cohomology remains bounded by one finite interval. No target meaning changes.

## Proved and sorry left

This is a zero-hole definition repair. Holes closed: 0. Holes added: 0. Holes remaining
in the restored module: 0. Split off: 0.

`AlgebraicGeometry.Scheme.coefficientEtaleBaseChange_isContinuous` remains proved by its
existing composition argument (node `def-pe-etale-constructible-module`). The eight other
declarations are real definitions/abbreviations, without sorry. No proof closure is claimed
for this repair, and no downstream theorem hole is changed.

## No longer needed

None. No imports, nodes, modules or declarations are withdrawn or pruned. All three
archived public imports are preserved, and the one new import provides the recorded
stratification used by the definition. No DAG or unit dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an item with sorry, but this assignment is a listed
zero-hole quarantine repair. The archived source uses the retired name
`LocallyClosedStratification`; its definition dependency was already repaired and records
`Scheme.FiniteLocallyClosedStratification`. Updating this consumer to that existing
interface fixes the compiler error without changing the mathematical predicate.
The source archive and its dependent archives are preserved, with their DAG attachments.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
