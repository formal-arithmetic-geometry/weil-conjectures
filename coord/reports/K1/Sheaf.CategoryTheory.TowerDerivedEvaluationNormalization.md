## What changed

Proved `CategoryTheory.exists_unique_towerDerivedEvaluation_normalized` in
`Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization`, preserving its statement,
all four independent derived-category universes, and every public definition and instance.
The proof builds the two normalized derived adjunctions with Mathlib's derived-adjunction
API. It extends the comparison of the two units from K-injective tower complexes using
`Localization.liftNatIso`, and proves normalization, uniqueness, transition compatibility
and the specified counit equation. All new helpers are private and proved.

The proof uses the existing proved generic `CategoryTheory.derives` from
`Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`. Added private imports
of that module and Mathlib's `Functor.Derived.Adjunction` and
`Functor.Derived.PointwiseLeftDerived`. Updated the item's DAG proof and dependencies
without changing its statement, attachment, or unit route.

Administrative change record:
`coord/changes/K1-tower-derived-evaluation-proof-environment.md` documents the extra
universe names for a private helper and theorem-scoped elaboration options requested
by static preflight. The downstream check finds no current Lean importers. All five
public interfaces and all public data bodies are unchanged; no consumer is adapted.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.exists_unique_towerDerivedEvaluation_normalized`
(node `lem-weil-pbc-tower-derived-evaluation-normalization`).
Holes added: zero. Sorries left in the delivery: none. No split-off statements.

Validation: the complete module compiled cleanly with `lcompile.py` in 13 seconds,
with zero remaining holes. The complete packet is submitted to `deliver3.py` for its
axiom probe and server preflight; the delivery tool records those final check results.

## No longer needed

Removed the direct proof imports `Sheaf.CategoryTheory.KInjectiveTotalDerived` and
`Sheaf.SixFunctors.ResolvingDerivedAdjunction`, and the redundant direct import
`Mathlib.Algebra.Homology.DerivedCategory.KInjective` (available through the used API).
The two named Sheaf modules are not used by this proof. No module is withdrawn, and
no claim is made that other parents no longer need them.

Removed `lem-sfb-resolving-derived-adjunction-normalization` from this node's proof
route: the exact left adjoint has an invertible localization comparison, so Mathlib's
absolute derived-adjunction API proves this case directly in independent universes.
Removed `lem-weil-pbc-kinjective-total-derived` from proof dependencies: the supplied
universal derived units are computed on K-injectives by the existing derivability
structure and `CategoryTheory.derives`; no new derived functor is chosen. This node
remains a statement dependency. The K-injective existence and Hom-localization nodes,
termwise adjunction, exact localization, levelwise abelianity and K-injective evaluation
remain needed. The proper-base-change unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The suggested resolving-class theorem has a common derived-category universe, whereas
this item permits four independent universes. Its exact-left-adjoint special case is
proved here with Mathlib's general API, keeping the item's statement verbatim. There
is no mathematical statement dispute.

During final verification the compile server temporarily stopped resolving Mathlib and
project imports, then repeatedly returned its busy-server timeout (exit code 124).
Earlier development compiles succeeded. The packet was retained and the prescribed
tools retried; the launcher scripts were not changed or bypassed.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
