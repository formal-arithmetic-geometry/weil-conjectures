## What changed

Completed the listed zero-hole retirement of
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient`
(`coord/retire-items.tsv`, row 1975). Its proved upstream owner is retained unchanged.
The old small-colimit module is withdrawn through `deleted.txt`; its node is
reattached to the exact upstream theorem signature.

Adapted the four direct consumers `RegularDivisorStrictLocalLimit`,
`StrictHenselRootNormalizationFinite`, `StrictHenselRootNormalizationGenericEtale`,
and `StrictHenselRootPurityData`. Each applies the upstream theorem after the
canonical colimit comparison, then explicitly transfers the three conclusions.
The existing `smallStrictHenselizationColimitIso_toBase` theorem supplies structural
compatibility. These are proved private helpers; no public wrapper replaces the item.
The original five public call sites now use their local transport helper.

The upstream helper collides with the old Sheaf structural-map helper. Replaced
the public structural-map import in six affected direct/transitive consumers with
the upstream module providing the identical definitions. The three transitive files
`StrictHenselRootTameNormalization`, `StrictHenselRootFiniteEtaleModel`, and
`RegularDivisorStrictHenselRootSection` change only that import. The strict-local-limit
proof uses the upstream residue theorem and transports its closed-point identity.
Four consumer nodes record the added comparison dependency. Every pre-existing
public signature, definition, declaration docstring and visibility is unchanged.

Change record: `coord/changes/A3-retire-strict-hensel-regular-divisor-quotient.md`.
All seven affected modules were unclaimed when checked.
`lcompile.py --all` compiles all seven individually in dependency order with exit 0
and no warnings (3.1–11.2 seconds per file). Public signatures, node field boundaries,
line widths, and absence of remaining imports of the retired module were checked.

## Proved and sorry left

This is a retirement repair with **0 original holes, 0 holes closed, 0 holes added,
and 0 split off**. The removed public declaration
`AlgebraicGeometry.Scheme.strictHenselization_regular_divisor_quotient` is preserved
on its proved upstream owner. Its four private small-model transports are fully
proved. All seven delivered consumer modules contain no `sorry`.

The unchanged public theorems are
`AlgebraicGeometry.Scheme.regular_divisor_strict_local_limit` and the
`AlgebraicGeometry.Scheme.GaloisCover` theorems
`strict_hensel_root_normalization_finite`,
`strict_hensel_root_normalization_generic_etale`, `strict_hensel_root_purity_data`,
`strict_hensel_root_tame_normalization`, `strict_hensel_root_finite_etale_model`,
and `strict_hensel_root_section`.

## No longer needed

Pruned module:
`Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient`.
Removed its private import from all four direct consumers and replaced it with
the proved upstream owner. The retired item's direct imports of upstream
`StrictHenselRegularDivisorQuotientNoetherian` and
`StrictHenselRegularDivisorQuotientRegular` are supplied by the upstream owner;
their mathematical nodes and modules remain needed.

Removed six public imports of
`Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap` from the affected closure.
Removed the private `Sheaf.Paper.StrictHenselizationFunctoriality` import from
`RegularDivisorStrictLocalLimit`; the upstream residue theorem plus canonical
transport supplies everything this proof uses. These shared modules have other
consumers and are not withdrawn here. No other node or module is claimed pruned.
All six DAG parents, including the two unfinished purity parents, retain the
regular-divisor quotient node. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an open `sorry`, but this assignment is the
explicitly listed retirement of a module with zero holes. A bare import replacement
fails: the canonical small and full colimits differ as Lean types, and the two
structural-map helper declarations also have a colliding name. The packet repairs
both issues and preserves all consumer statements; it does not weaken the theorem.
Searches with `msearch.py` (Lean Finder, Loogle, grep) and local source search found
the existing upstream result and Mathlib transport API. No new node is needed.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
