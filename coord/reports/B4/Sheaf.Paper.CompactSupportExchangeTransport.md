## What changed

Proved `AlgebraicGeometry.ProEtale.compactSupport_exchange_transport` in
`Sheaf.Paper.CompactSupportExchangeTransport`. The proof follows all four DAG steps:
normalize the compact-support comparison into its proper and open factors, apply
`comparison_derivedBaseChangeMap` and `fixSiteOpenExchange`, compose their equations
using naturality, and cancel the witness isomorphism by naturality of the ambient
exchange. The etale formalism's open mate is identified with exact derived open
base change using its unit equation.

All four public definitions, the theorem signature, and the public imports are
unchanged. Private, fully proved categorical helpers normalize bounded-below
inclusions, exact derived squares, restricted adjunction units, inverse mates and
horizontal composition. Added elaboration options, local exact-composition instance
attributes and scoped helper variables are documented in
`coord/changes/B4-compact-support-exchange-proof-scope.md`. Keeping these
calculations generic avoids expensive unfolding of the concrete module-sheaf constructions. Added proof-only imports
`Sheaf.CategoryTheory.DerivedExactSquare` and
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.

Validation: the complete module compiled successfully in 27.1 seconds through
`lcompile.py`. Removed the three reported unused simp arguments. The new imports
pass both import-direction checks. The first dry run required a change record for
proof-scope commands; `coord/changes/B4-compact-support-exchange-proof-scope.md`
records them and all downstream consumers. No consumer is adapted. The second
dry run passed compilation and preflight (temporary commit `c6510db58b`); the
delivery is classified CODEX for independent review.

## Proved and sorry left

The original single hole is in
`AlgebraicGeometry.ProEtale.compactSupport_exchange_transport`
(`lem-pur-co-smooth-exchange-transport`). This hole is closed by a compiling proof.
Its replacement and every private helper contain zero `sorry` tokens. Original
holes: one; proved: one; left: zero. Holes added: zero. Split-off statements: zero.
No new axioms, public statements or definitions are introduced. Existing named dependency theorems
are used with their recorded statements, as required for stage 3.

## No longer needed

Removed three proof-only imports from the shared source:

- `Sheaf.AlgebraicGeometry.FiniteOpenBaseChangeNormalized`: its strict-tower
  coefficient interface is unnecessary for the ordinary fixed-coefficient square;
  the proof uses `ProEtaleDerivedExtensionZeroBaseChange` instead.
- `Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness`: the statement already supplies
  the antecedent and its isomorphism explicitly; ordinary naturality proves the
  witness assertion.
- `Sheaf.Paper.ExchangeProjectionSuppliedDomains`: the ambient exchange is already
  the specified compactification composite from the imported finite-coefficient
  lower-shriek base-change module.

Static import-closure comparison removes `FixedEtaleOriginWitness` and
`ExchangeProjectionSuppliedDomains` from this item’s closure. Other target paths
still import them; no module leaves the overall `TargetsCheck` closure.
`FiniteOpenBaseChangeNormalized` remains reachable transitively.

No DAG dependency is bypassed: the four-step route, its proper and open comparison
nodes, and the blueprint unit route are retained. These import removals remove
unneeded parallel interfaces, not the corresponding mathematical ingredients.

## Where the brief, the DAG or earlier work was wrong

The retained earlier draft had no textual holes but did not compile. This
continuation repaired the bounded-below inclusion normalizations, the identification
of the formalism's inverse open mate, and the reassociations in the proper/open
composition. Earlier reports of unavailable compiled artifacts are obsolete; current
checks reach the proofs. Specialized rewrites also caused kernel timeouts; generic
categorical helpers replace those expansions without changing any definition or
raising a compiler limit. No mathematical statement or DAG step was disputed.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
