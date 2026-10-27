## What changed

Proved `WeilConjectures.FiniteMateDomain.finiteMateDomain` in
`Sheaf.Paper.FiniteMateDomain`, preserving its signature and all public imports.
Added two proved private arithmetic helpers: `coefficient_annihilator` proves
`(ell^n : A_n) = 0` by membership in the nth power of the maximal ideal;
`prime_unit` maps the unit ell from the characteristic-p base field into global
sections. Proper base change now uses the existing module-valued theorem
`Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`. Smooth base change uses
`Etale.isIso_baseChange_app_of_smooth_of_isTorsionSheafOfInvertibleOrder`, with
`of_natCast_eq_zero` supplying its cohomology hypothesis. The specified
coefficient-forgetting equation and site-comparison equation come from their
existing dependency declarations. A proved private categorical helper,
`conjugate_exchange`, uses naturality and cancellation to prove the exact
five-factor retained-witness formula, whose factors are isomorphisms.

Updated the node's proof, proof dependencies and proof origin to match this
argument. The proper/smooth bounded-below base-change and subsequent site
transport route of the unit is retained. No public interfaces, definitions,
consumers or source-library modules change.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.FiniteMateDomain.finiteMateDomain`
(node `lem-sf-bc-finite-mate-domain`). No holes added or split off. No `sorry`
remains in the delivered Lean module. All three new private helpers are fully proved.
The proof uses existing dependency declarations; this does not claim their
transitive proofs are free of `sorry`.

## No longer needed

Removed proof-only imports:

- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange`
- `Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets`
- `WeilConjectures.SixFunctors.BaseChange.Derived`

Retained `ExtensionIntegersDvr`, `SpectralNorm`, `Separated`, and the proper
base-change import. Added the proof import
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived` for its already proved
module-valued bounded-below smooth theorem.

Removed direct proof dependencies:

- `lem-weil-valued-dvr-finite-quotients`: annihilation gives additive torsion
  directly; quotient finiteness is unnecessary.
- `def-weil-finite-type-morphism`: quasi-compactness is explicitly supplied in
  the theorem signature; no conversion from finite type is needed.
- `lem-weil-pbc-qcqs-morphism-permanence`: both vertical edges already have
  quasi-compactness and separatedness hypotheses.
- `sbc-thm-bounded-below-derived-smooth-base-change`: the existing direct
  module-valued bounded-below theorem applies before coefficient forgetting.
  Its actual sheaf-theorem dependency `sbc-thm-smooth-base-change` is recorded
  instead, matching the proof of the source theorem in SmoothBaseChange.Derived.
- `sbc-def-base-change-map`: no abelian allowable-torsion wrapper conversion
  is needed to prove invertibility. The explicitly requested abelian equation
  is still obtained from `exchange_forget_coefficients`.

These are direct dependency/import removals for this proof. All original public
imports remain; no claim is made that the removed modules have no other users.
The source library is untouched, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient finiteness and ramification-exponent argument is longer
than needed: ell belongs to the maximal ideal, so ell^n already belongs to its
nth power. This works even at n=0 (the zero quotient), though the theorem keeps
its original positive-level hypothesis. The field-unit argument also permits
empty schemes since units map to units in the zero global-sections ring.

The library already provides the module-valued bounded-below proper and smooth
maps needed here, so proving invertibility via the separate abelian wrapper is
unnecessary. The coefficient-forgetting and site-comparison identities remain
statements about the exact canonical arrows in the original signature.
Smoothness is used for g, qcqs for f, with output Y-prime. The smooth argument
works for all D+ antecedents; its specialization to the stated bounded
constructible witnesses needs no change to the statement and asserts no
constructible landing of either endpoint.

No rework/return entry for this item was found. Search logs in the sandbox
record semantic, type-pattern and grep searches; the semantic hits concern
scheme morphisms rather than derived exchange. Existing source declarations
supply the shorter route. No new nodes or statement/definition repairs.

The final categorical calculation is proved generically in `conjugate_exchange`
and then applied to the derived mate. This avoids elaborator expansion of the
derived functor definitions during associativity rewriting. No elaboration
settings or compile limits are changed. The final file compiles cleanly in 31 seconds.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
