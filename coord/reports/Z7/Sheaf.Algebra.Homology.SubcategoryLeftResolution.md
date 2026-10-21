## What changed

Proved `CochainComplex.exists_subcategory_left_resolution` in
`Sheaf.Algebra.Homology.SubcategoryLeftResolution` without changing its statement or public
imports. The proof implements Stacks Project Tag 05T7(1), `derived.tex`, lines 5300–5376.
Private helpers construct the descending kernel-pullback tower from independently chosen
covering epimorphisms, assemble its integer-indexed terms, and prove both projection equations.
The bookkeeping specializes the already proved upstream `CyclePullbackTower`,
`CyclePullbackLaws`, and `CyclePullbackTowerComparison` constructions to objectwise covers;
none of those source files is changed. The given zero object is used literally above the
bound, so no isomorphism-closure assumption on the covering class is introduced.

Added proof imports `Mathlib.Algebra.Homology.Refinements` and
`WeilConjectures.Algebra.Homology.CyclePullbackLifting`. The latter's proved
`CochainComplex.cyclePullback_lifting_pointwise` supplies simultaneous lifts of compatible
pairs; Mathlib's refinement criteria then prove homology-map monicity and epicity and
componentwise epicity. This is an existing proved tool lemma from another unit, not a
replacement for a unit's route. Updated the existing node's proof, proof dependencies and
proof origin to describe the implementation. No public interface change, consumer adaptation, or
new module is needed. Preflight conservatively classifies the added helper namespace and
scoped commands as an interface change; their scope and all eight downstream consumers are
documented in `coord/changes/subcategory-left-resolution-private-commands.md`. No consumer
adaptation is required; all public signatures and imports remain identical.

Validation: the completed module compiled cleanly through `lcompile.py` in 3.8 seconds on the resumed attempt,
with no warnings. The theorem's original signature is byte-for-byte unchanged; all Lean
lines meet the 100-character bound and the node's proof dependencies equal the union of
its steps' uses. The new proof import was checked to create no import cycle.

## Proved and sorry left

Closed the one original hole:
`CochainComplex.exists_subcategory_left_resolution`
(node `lem-sfb-subcategory-left-resolution`).

Holes closed: 1. Holes added: 0. Sorries left in the delivered module: 0.
Every private construction and helper proof is complete; no results are split off.

## No longer needed

Replaced the direct proof import `Mathlib.CategoryTheory.Abelian.Refinements` with
`Mathlib.Algebra.Homology.Refinements`, which imports it and additionally exposes the
complex-level homology-map criteria used by the proof. No mathematical dependency is pruned:
both definition dependencies and `lem-sp-abelian-refinements` remain used. No node or module
is withdrawn or made unnecessary by this delivery. The functorial resolution modules inspected
in the search are not imported: their additional functorial-cover or closure assumptions are
not available here. No unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The original seven-step plan maintains
cycle epimorphisms and cohomology isomorphisms during induction. The implementation constructs
the same descending pullbacks first and then checks those consequences through simultaneous
lifting. The updated node records this equivalent argument. In particular, it does not assume
that the class contains Mathlib's chosen zero object, only the zero object provided by `hzero`.

Previous attempt infrastructure failure: two invocations of the required `deliver3.py Z7
Sheaf.Algebra.Homology.SubcategoryLeftResolution` terminated with exit code 137 before
printing a check result or `DELIVERED`. The first printed a shared-fetch wait before
termination; the second printed no diagnostic. A read-only remote branch lookup after
each termination succeeded and confirmed that the delivery branch is absent. The proved,
cleanly compiling packet remains in this sandbox; no launcher scripts were modified.

Resumed attempt: the required delivery check reached server preflight and requested the
change record above for helper commands (`variable`, `omit`, and declaration-local options).
Added that record with the unchanged signature, scoped commands, and full downstream list.
An additional `lcompile.py` request returned no answer within 210 seconds (busy server),
so that request is not counted as a compile result. A later retry compiled cleanly in
3.8 seconds with exit code 0, and the import-direction check also passed. No Lean edits
were needed on resumption.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
