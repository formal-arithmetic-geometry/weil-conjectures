## What changed

Proved `WeilConjectures.normalizedDVRModuleRes_exact` in
`Sheaf.Paper.NormalizedDVRTower`. A private, fully proved general lemma establishes exactness
of scalar restriction for arbitrary ring sheaves with independent universes. After forgetting
to abelian sheaves the composite is definitionally the source forgetful functor; Mathlib's
reflection lemmas recover finite-limit and finite-colimit preservation. Specialize to the
actual quotient map. No existing signature, definition, visibility or target changed.

Added the proof-only import
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` for its existing,
sorry-free finite-colimit preservation instance. Updated the node's proof fields to record
this argument. The unit's statement and route remain unchanged.

The final module compiled through `lcompile.py` in 14.8 seconds with no errors or warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.normalizedDVRModuleRes_exact`
(node `def-coef-normalized-dvr-tower`).

Added 0 holes. No `sorry` remains in the delivered module. The private helper
`normalizedDVRRestrictionExact` is fully proved. This is a proof, not a decomposition.

## No longer needed

Removed the unused proof imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
  (`lem-pur-derived-change-of-rings`).
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
  (`lem-pc-pre-derived-adjoint-functors-general`).

Neither theorem is needed to construct the tower structure or prove scalar-restriction
exactness: normalization is already expressed by the universal Hom property. Their
mathematical role in explaining the equivalence with the adjoint comparison remains in
the unchanged statement-dependency record. No other imports or declared proof dependencies
are unused; no module is withdrawn. These imports may remain reachable through other parents.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The definition node had no proof steps despite recording the
finite-restriction exactness helper; its proof fields now describe that helper's proof.
Direct specialization of the forgetful argument triggered a deterministic kernel timeout
while comparing the large coefficient constructions. Generalizing the argument before
specializing eliminated that issue without changing any definition or compiler limit.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
