## What changed

Proved `CategoryTheory.Functor.exactAdjointForgetDerivedDetection` with its entire signature
unchanged in `Sheaf.CategoryTheory.ExactAdjointForgetDerivedDetection`.
The existing adjunction lemmas give preservation of injectives and K-injectives; Mathlib gives
triangulation and the single-degree comparison. The existing normalized natural homology
isomorphism gives the representative formula. `NatIso.isIso_map_iff` transports invertibility
of derived homology maps to `U(H^r(f))`; reflection through U and
`DerivedCategory.isIso_iff` finish detection. `U.mapHomotopy` proves the homotopy clause.
The same detection proof supplies the `ReflectsIsomorphisms` structure.

Updated the node's proof, proof dependencies and proof origin to this shorter route.
The source statement, universes, unit route and existing definitions are unchanged.
See `coord/changes/H1-exact-adjoint-forget-unused-resolution-import.md` for the unused public
import removal and consumer check. There are no importers or external declaration users to adapt.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.Functor.exactAdjointForgetDerivedDetection`
(node `lem-sf-exact-adjoint-forget-derived-detection`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.
The proof uses existing proved declarations, with no new assumptions or definitions.
The module compiles on the project server; delivery also runs its axiom probe.

## No longer needed

Removed the private import `Sheaf.CategoryTheory.ExactDerivedCohomologyCoherence` and its
proof dependency and obsolete tool-use approval `lem-pur-exact-derived-cohomology-coherence`:
this item needs the normalized comparison and its representative formula, already proved in
`WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, rather than the
stronger compositor-coherence theorem. Its original docstring describes the earlier plan;
the updated DAG records the proof actually used.

Removed the unused public import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`: no resolution functor is
needed by the statement or proof. Its definition node `def-sfb-right-derived-functor` stays
in the conceptual statement dependencies, but its Lean module is not needed by this proof.
No module is withdrawn, and no parent proof or unit step is pruned. These are local import
and proof-edge removals; other consumers can still need these modules and nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or missing hypothesis was found. The original step 3 cites stronger
coherence than required: the normalized natural isomorphism and representative formula
already exist as proved upstream declarations. Identity adjunctions, zero categories and
all integer degrees are covered without extra hypotheses. The Lean proof is polymorphic
in the unchanged independent category, morphism and derived-category universes.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
