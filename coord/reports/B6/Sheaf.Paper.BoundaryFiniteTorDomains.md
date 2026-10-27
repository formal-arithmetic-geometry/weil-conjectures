## What changed

Filled `WeilConjectures.boundary_finite_tor_domains` without changing its signature or any
of the three domain predicates. Added four proved private helpers: the bounded-constructible
predicate comparison, its finite-Tor version, invariance under isomorphism, and a natural costalk comparison obtained by
conjugating the source library's natural Verdier exchange with its adjunctions. All new
imports are private proof imports. No source-library file is changed.

For geometry, Mathlib directly gives local finite type for an immersion; its topological
embedding into the Noetherian ambient space gives quasi-compactness. The existing source
ambient adjunction and bounded-below exceptional restriction supply the structure-map clauses.
Finite-stage geometric biduality supplies preservation by duality and the specified biduality
map. After translating the constructibility predicates, the proved source pullback theorem
supplies ordinary restriction. The costalk comparison composed with exceptional restriction
of biduality identifies `G L` with `DZ (s (DT L))`; closure under isomorphism proves exceptional
preservation. The two canonical dualizing isomorphisms and the existing composition theorem
supply the final clauses.

Read the current blueprint proof at
`literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`cor-weil-boundary-duality-discharge.proof.md`. The unit's realized statement and steps are
empty; the geometric-biduality/costalk route is retained. Predicate comparison widens the
interval to `[min a b,b]`, so zero complexes and unrelated original bounds are covered.
Empty pieces, the identity closed immersion, and every positive coefficient level are included.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.boundary_finite_tor_domains`
(node `lem-weil-boundary-finite-tor-domains`). Added 0 holes and split off 0 statements.
No `sorry` remains in the delivered module. Each of the four new private helpers is proved.
The theorem still depends on the recorded finite-stage geometric-biduality and
boundary-dualizing-composition declarations; their existing dependencies are unchanged.

## No longer needed

Removed these private proof imports:

- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`
- `Mathlib.AlgebraicGeometry.Morphisms.Separated`
- `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`
- `Sheaf.Paper.BoundaryEtaleAdjunctionRestriction`
- `Sheaf.SixFunctors.ClosedCostalkDuality`
- `Sheaf.Paper.EtaleTorFlatPullbackModel`
- `WeilConjectures.SixFunctors.Etale.Derived.BoundaryDuality`

Removed direct DAG proof dependencies:

- `lem-weil-pbc-noetherian-open-subscheme-noetherian` and
  `lem-weil-pbc-qc-open-immersion-finite-type`: the embedding into the Noetherian ambient
  space proves quasi-compactness directly; Mathlib already infers local finite type.
- `lem-weil-pbc-closed-immersion-proper`: no separate properness argument is needed to
  establish finite type of an immersion; the existing Mathlib instances handle closed maps.
- `lem-weil-boundary-etale-adjunction-restriction`: the source ambient adjunction and
  `plus_rightDerivedUpperShriek_obj` already state the two needed clauses.
- `prop-weil-pbc-inverse-image-modules-exact`,
  `lem-pur-scheme-constructible-preimage`, and `lem-sf-etale-tor-flat-pullback-model`:
  the proved source `constructibleFiniteTor_mapDerivedCategory_upperStar` already gives
  ordinary restriction after identification of the predicates. Removed the obsolete
  top-level tool-use approval for the first of these.
- `lem-weil-closed-costalk-duality`: the natural costalk comparison is constructed from
  the source natural tensor-Hom/Verdier exchange and uniqueness of right adjoints,
  directly in the constant-module categories.

These are direct dependencies removed from this item's proof, not a claim that all their
modules leave the targets' entire transitive closure. No module is withdrawn.
All public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

The planned flat-model/stratification proof is unnecessary because the source library has
already proved pullback preservation. Its constructibility predicate is equivalent to the
one used here, as the private helpers prove. Likewise the ambient adjunction and its D+
preservation are already available as source declarations. The ringed costalk theorem need
not be transported into the constant-module categories: the source natural Verdier exchange
and its self-adjunctions give the required natural isomorphism by conjugation. No statement
repair or definition repair was required. The DAG proof and proof dependencies now record
this route. No new nodes or change records are needed.

## Second reading by B6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
