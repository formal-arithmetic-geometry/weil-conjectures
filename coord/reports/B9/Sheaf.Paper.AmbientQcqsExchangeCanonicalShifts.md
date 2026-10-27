## What changed

Proved all three theorems of `Sheaf.Paper.AmbientQcqsExchangeCanonicalShifts` without changing
any public declaration signature, definition, universe, or public import. Added private proof
imports of `Sheaf.Paper.KFlatDerivedAdjunctionTransportShifts` and
`WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction`.

Three proved private helpers specialize the existing adjunction transport theorem to
`Mon.mk Λ`, identify the actual ambient pullback square with the published shift-compatible
square, and apply the source library's `NatTrans.CommShift.mateEquiv`. The composite
triangulated instances and the component shift equation then prove the first theorem.
The second theorem extracts the unit and counit shift instances and the square assertion.
The third explicitly constructs the triangle morphism: naturality gives the first two
squares; the shift equation at one followed by naturality at the connecting arrow gives
the third. This retains arbitrary schemes and ordinary unbounded derived categories.

Validation: the complete module compiled through `lcompile.py` with exit code zero in
22.3 seconds, with no Lean errors or warnings. The import-direction checks accepted both
new proof imports. A textual scan found no remaining `sorry` or forbidden declaration form.

The node proof, proof dependencies and proof origin now describe this Lean argument.
The compactification-coherence unit's statement and route are unchanged.

## Proved and sorry left

Closed all three original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.ambient_qcqs_exchange_canonical_shifts`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ambient_qcqs_exchange_canonical_normalization`.
- `AlgebraicGeometry.ProEtale.CondensedRing.ambient_qcqs_exchange_distinguished_triangle`.

All belong to `lem-sfb-ambient-qcqs-exchange-canonical-shifts`. Zero holes remain in the
item, zero holes are added, and zero statements are split off. These are proofs from the
existing declared dependencies, including the currently unfinished functor/compositor and
adjunction normalization theorems; they do not claim those dependencies are axiom-free.

## No longer needed

Removed the private imports `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations` and
`Sheaf.Paper.IntegralFinitePullbackComposition`. The proof uses the actual condensed
module-object exchange and its already-stated compositor shift equation, so it needs no
conversion through the separate ring-sheaf operations or integral-tower presentation.
Consequently `def-weil-pbc-proetale-operations` and
`lem-weil-pbc-proetale-derived-pullback-composition` are removed from this node's proof
dependencies and proof-step uses. Its statement dependencies are unchanged.

Removed the redundant direct private import of
`Sheaf.Paper.ModuleDerivedFunctorCompositorShifts`: it is still publicly reexported by the
unchanged `Sheaf.Paper.ModuleDerivedFunctorShifts` import and is used by the proof, so its
node remains a proof dependency. No other node is pruned, no file is withdrawn, and no
claim is made that the removed dependencies are unused by the rest of the library.

## Where the brief, the DAG or earlier work was wrong

The plan's conversion through the ring-sheaf and integral-pullback interfaces is unnecessary:
the actual exchange is already definitionally a mate of the published condensed pullback
square. The source-library shift-compatible mates theorem performs precisely the
unit-square-counit closure calculation proposed by the plan. This shortens its assembly
without bypassing the two canonical normalization results or the unit route.

Lean needs explicit named functor arguments when synthesizing shift structures for natural
transformations whose types otherwise expose the generic left/right derived functors.
The same explicit interfaces are used in the connecting-arrow naturality equation.
No mathematical statement or definition repair was necessary. The resumed sandbox initially
contained only dispatcher metadata, with no saved proof packet or delivery result.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
