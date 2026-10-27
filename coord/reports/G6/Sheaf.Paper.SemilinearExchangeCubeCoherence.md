## What changed

Proved `WeilConjectures.PodExchangeCube.relabeling` in
`Sheaf.Paper.SemilinearExchangeCubeCoherence`, without changing its signature,
definitions, or docstring. After unfolding only `twist`, Mathlib supplies
`LocallyOfFiniteType (gW.hom ≫ W.hom)` and `QuasiCompact (gW.hom ≫ W.hom)`
by composition, since `gW.hom` is an isomorphism. Associativity, `hg`, and `hr`
prove the remaining arrow equation. Neither structural separatedness nor a
finite-type hypothesis on V is needed.

The complete module compiled through `lcompile.py` in 17.6 seconds before unused
private imports were removed. The final import-pruned version compiled cleanly in 26.8 seconds;
`deliver3.py` performs the final delivery checks. The final delivery contains only this module and
this report.

Searches run through `msearch.py`: Lean Finder for finite-type/quasi-compact
composition (found the two composition instances and isomorphism finiteness),
Loogle for `CategoryTheory.mateEquiv_vcomp` (found the generic mate lemma), and
grep for `locallyOfFiniteType_comp|quasiCompact_comp` (found both Mathlib
instances). Read the assigned node's eight proof steps, the dependency Lean
records, the supplied exchange/datum signatures, and the latest blueprint's
`lem-fix-weil-operations.proof.md` and `prop-weil-operations.proof.md`.

## Proved and sorry left

Closed one of the module's original three holes:
`WeilConjectures.PodExchangeCube.relabeling`.

Two original holes remain unchanged, both attached to
`lem-pod-semilinear-exchange-cube-coherence`:

- `WeilConjectures.PodExchangeCube.rational_coherence`.
- `WeilConjectures.PodExchangeCube.common_coherence`.

Added zero holes and split off zero statements. This is a partial proof delivery,
not a proof of either coefficient-stage coherence package.

## No longer needed

Removed these private imports, which the completed relabeling proof and the
existing statements do not use:

- `Sheaf.Paper.ExchangeFunctoriality`.
- `WeilConjectures.Compactification.RefinementCategory`.
- `Mathlib.AlgebraicGeometry.Sites.Proetale`.

No DAG node or library module is withdrawn. In particular,
`fix-lem-exchanges` and the compactification dependencies remain in the proof
plan for the two unfinished coefficient-stage theorems. No claim is made that
these dependencies have become mathematically unnecessary.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The module has three holes: the geometric
`relabeling` theorem in addition to the two coefficient-stage packages.
Its existing docstring gives a direct Mathlib proof, which is now formalized.

The remaining work is not blocked by dependencies containing `sorry`.
`exchangeFunctoriality` states laws for the published canonical coefficient
operations; applying them to this item's `Laws` requires transporting those
maps through the supplied datum's adjunction, composition, compactification,
and coefficient normalizations. This delivery does not claim that transport
has been formalized and leaves both original theorem bodies unchanged.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
