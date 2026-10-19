## What changed

Filled `AlgebraicGeometry.ProEtale.smoothMate_counit_cancellation` with a categorical
proof of all its clauses. Private, proved helpers identify the exchange, cancel the
comparison maps, identify the transposes, establish invertibility of the target unit,
and prove the three naturality equations. Every existing public signature, definition,
docstring and public import is unchanged. No other Lean module is changed.

The node copy records the actual five-step proof route and its dependencies.
The change record `coord/changes/G4-smooth-mate-private-proof-context.md` documents
the declaration-scoped private proof commands flagged by static preflight and all
163 transitive consumers; their public interfaces need no adaptation.
The final module compiles cleanly through `lcompile.py` (20.1 seconds, exit code 0).

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.smoothMate_counit_cancellation`
(node `lem-pur-smb-mate-counit-cancellation`) is proved by a complete, compiler-checked proof. Holes closed: 1 of 1.
Holes added: 0. Sorries left in the delivered source: 0. Split off: 0.
Every private helper is proved in this module.

## No longer needed

Removed these seven redundant proof-only imports:

- `Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange`

The compactification, exchange, compact-support comparison and pullback comparison
interfaces remain available through the unchanged public imports; their nodes stay
in the proof dependencies. In particular, removing these redundant direct imports
does not claim that all their modules leave the targets' import closure.

Removed three nodes from this item's proof dependencies:
`thm-amb-etale-exceptional-adjoint`, `thm-sf-ambient-adjoint-class`, and
`def-weil-exceptional-inverse-image`. The theorem supplies the ordinary adjunctions,
and `mateCounitProTranspose` already spells out the normalized Hom formula. Thus
this proof needs neither adjoint existence theorem, the constructed class-restricted
Hom equivalence, nor the coefficient system. Their owning modules are respectively
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`,
`Sheaf.AlgebraicGeometry.SpecifiedExceptionalClassHom`, and
`Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`. Existing statement
dependencies and the unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The old plan invoked adjoint-existence and class-adjunction results even though the
Lean statement supplies the adjunctions and the explicit normalized transpose.
Generic adjunction naturality from Mathlib suffices for that part of the argument.
No mathematical defect or signature change was required. The preserved draft's
naturality proof needed explicit expansion of the compact-support functor map;
the cancellation proof needed cancellation of the mapped comparison isomorphism
before applying pullback-comparison naturality.

Earlier compilation attempts, including the resumed dry runs, received no answer
from the compile server. The latest `lcompile.py` call compiled the final repaired
module cleanly in 20.1 seconds. No new nodes or definition repairs are included.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
