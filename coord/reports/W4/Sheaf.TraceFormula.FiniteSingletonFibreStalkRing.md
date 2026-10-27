## What changed

Proved `AlgebraicGeometry.finite_singleton_fibre_stalk_ring` without changing its statement.
The proof follows both existing DAG steps and Stacks Tag 05B8(2)(3): take an affine
neighbourhood and its affine inverse image; use the singleton fibre to prove uniqueness
of the prime over the base prime; use `IsLocalization.uniquePrimeLocalization` to give
the target prime localization the base-complement localization structure. Mathlib's
`IsAffineOpen.arrowStalkMapIso` identifies the actual stalk map, and the two localization
preservation theorems give finiteness and finite presentation. Finally enumerate a
finite generating family of the presentation ideal to obtain the required polynomial
quotient algebra equivalence. A proved private helper extracts the ring-localization
clause of the existing unique-prime theorem.

## Proved and sorry left

Closed 1 of 1 original holes: `AlgebraicGeometry.finite_singleton_fibre_stalk_ring`
(node `lem-trf-finite-singleton-fibre-stalk-ring`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The existing imported theorem
`IsLocalization.uniquePrimeLocalization` remains an upstream proof dependency with
its existing hole; its module is not modified. Thus this delivery proves the assigned
statement from its declared dependencies, rather than claiming an axiom-free closure
of that dependency.

## No longer needed

Removed proof import `WeilConjectures.Topology.PresheafModuleStalkFunctor`: the theorem
uses scheme ring stalks directly from Mathlib, not the module-valued stalk functor.
No mathematical dependency of the two planned DAG steps is bypassed; no node or module
is withdrawn. In particular `Sheaf.RingTheory.UniquePrimeLocalization` remains needed.
No new imports are added. The existing public imports are preserved.
The diagnostic-option removal is recorded in
`coord/changes/finite-singleton-fibre-warning-option.md`, including all 55
downstream modules; none needs an adaptation.

## Where the brief, the DAG or earlier work was wrong

Repaired return for head `55d96d8c463`: removed the obsolete file-level
`warn.sorry` option, whose option-name token was counted as an unattributed hole
by the landing ledger. The proof and theorem signature are unchanged by this repair.
No mathematical correction was required. The declared affine comparison and
localization dependencies suffice. LeanFinder, Loogle and grep searches found no
existing theorem giving this singleton-fibre stalk-map conclusion directly.
The unit route is unchanged. The singleton hypothesis is used to identify every prime
over the base prime, and finite presentation is used only in the second conjunct.
The presentation construction allows zero variables and zero relations.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
