## What changed

Completed the retirement listed in `coord/retire-items.tsv` for
`Sheaf.RingTheory.SerreCriterionNormal`. Withdrew the duplicate module and redirected
its DAG node to `WeilConjectures.RingTheory.SerreCriterionNormal`, declaration
`Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS`.
The source theorem has exactly the duplicate's hypotheses, universes and conclusion.
Its proof and the node's existing proof route agree; neither changes.

Changed the three current direct consumers to import the upstream module:
`Sheaf.Paper.NormalLocusAssociatedPrime`,
`Sheaf.RingTheory.CompleteToricBoundaryClassInjectivity`, and
`Sheaf.TraceFormula.CompleteToricKatoRecognition`.
The two applications in `NormalLocusAssociatedPrime` now use the upstream name.
All consumer declaration signatures and public imports are preserved.
No upstream file or target statement is changed, and no copy of a landed theorem is added.

Read both complete Serre-criterion modules and checked the common statement against
Stacks Algebra Tag 031S in the local source. LeanFinder and Loogle searches returned
only related Dedekind-domain/DVR results; local source search identified the exact
upstream replacement. All three adapted modules were compiled together through
`lcompile.py --all`; delivery also performs its compiler and axiom checks.

Change record: `coord/changes/retire-serre-criterion-normal-r1.md`.

## Proved and sorry left

The item initially contained zero `sorry`s. Holes closed: zero. Holes added: zero.
No theorem is decomposed and no new node is introduced.
The duplicate `Ring.serreCriterionNormal` is withdrawn in favor of the already proved
upstream theorem, with its node retained and reattached.

The two existing consumer holes are unchanged:
`AddMonoidAlgebra.completeToric_boundaryClass_injective`
(`lem-trf-complete-toric-boundary-class-injectivity`) and
`complete_toric_kato_recognition` (`lem-trf-complete-toric-kato-recognition`).
`AlgebraicGeometry.exists_nonNormal_associatedPrime_le` and its private helpers
remain proved.

## No longer needed

Pruned module: `Sheaf.RingTheory.SerreCriterionNormal`, including its duplicate
declaration `Ring.serreCriterionNormal`.
Removed its private import from each of the three consumers named above; each now
imports `WeilConjectures.RingTheory.SerreCriterionNormal`.
The other three consumers recorded in the retirement inventory
(`Sheaf.RingTheory.NormalDomainPrincipalQuotientAssociatedHeight`,
`Sheaf.RingTheory.NormalOfFlatNormalFibers`, and `Sheaf.RingTheory.RegularRingNormal`)
had already been retired and are absent from the current tree.

No mathematical proof dependency is pruned: the upstream theorem preserves the
existing proof and all its dependency modules. The blueprint unit's statement and
steps are untouched. No declaration is removed from `lean/WeilConjectures/`.

## Where the brief, the DAG or earlier work was wrong

This is a queued retirement rather than an open proof: the item has no direct holes.
The DAG's declaration already used the upstream theorem's name while its module and
file still pointed at the duplicate defining `serreCriterionNormal`.
The attachment now consistently points at the adopted source theorem.
The retirement inventory listed six consumers; the current tree has three.
No mathematical statement or definition required correction.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
