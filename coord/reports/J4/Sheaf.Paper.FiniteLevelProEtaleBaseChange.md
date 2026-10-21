## What changed

The assigned theorem `AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange` is now proved.
Its proof applies the canonical function-to-constant coefficient restriction, uses the
intermediate transport theorem, and reflects isomorphisms through exact conservative
restriction of scalars. The proof-only scalar-extension import is used to obtain the derived
reflection instance.

Added `Sheaf.Paper.FiniteCoefficientExchangeTransport`, whose transport theorem is the one
remaining independent result needed by the proof. Updated the assigned node to record that
dependency and the new intermediate node. Removed five unused proof imports from the assigned
module.

## Proved and sorry left

Closed `AlgebraicGeometry.Scheme.finiteLevelProEtaleBaseChange` (the assigned hole).

The new theorem
`AlgebraicGeometry.Scheme.finiteOriginToConstant_map_ambientExchange_isIso` remains one
`sorry`, recorded by node `lem-weil-pbc-finite-origin-exchange-transport`. It is a strict
coefficient-transport subresult: it asserts invertibility only after applying the canonical
function-to-constant restriction and allows arbitrary compatible coefficient identifications.
Its stated route uses the existing ring-sheaf change-of-rings adjunction compatibility.

## No longer needed

Removed these proof-only imports from the assigned module because the final proof does not use
their declarations:

- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`
- `Sheaf.Paper.CondensedAmbientExchange`
- `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`
- `WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange`

The corresponding lower-level nodes are not needed by this Lean route. No public import needed by
the assigned declarations was removed.

The new transport module also omits a duplicate public import of
`Sheaf.AlgebraicGeometry.ProEtaleAmbientRingedExchange`, since it is re-exported by
`Sheaf.Paper.FiniteLevelRingedProEtaleBaseChange`.

## Where the brief, the DAG or earlier work was wrong

The original proof paragraph leaves the change from continuous-function coefficient modules to
constant coefficient modules implicit. The available fixed constant-coefficient theorem applies
only after that restriction, so the transport step must be isolated as a separate statement.

## New nodes

`lem-weil-pbc-finite-origin-exchange-transport` is implemented by
`Sheaf.Paper.FiniteCoefficientExchangeTransport` and records the remaining transport proof.

The public module and theorem addition is recorded in
`coord/changes/finite-level-proetale-base-change.md`.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
