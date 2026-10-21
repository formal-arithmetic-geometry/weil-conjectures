## What changed

Filled `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality`
in `Sheaf.SixFunctors.SchemeGeometricFrobenius` using the existing factorized-pullback
pasting theorem and the arbitrary-pullback clause of the Frobenius trivialization.
A proved private helper identifies the chosen Frobenius compositor with the published
canonical compositor: the adjunction unit-section equation determines the ordinary
comparison, and the existing normalization theorem identifies its derived descent.
Two further proved private helpers transport pasting through the actual factorizations
and perform the final componentwise naturality calculation. All existing public
signatures, definitions, and public imports are unchanged. Added one private proof
import of `Sheaf.AlgebraicGeometry.FactorizedProEtalePullbackPasting`.
Updated `def-pur-scheme-geometric-frobenius` to describe the proof actually used.
Change record: `coord/changes/J2-scheme-geometric-frobenius-proof-context.md`.
The first server preflight requested this record for the local proof-context commands;
it is included with the consumer audit (no current Lean importers).
The complete module compiled on the server in 26.7 seconds; a documented local
heartbeat allowance covers the dependent derived-functor normalization. The
60-second single-file limit is unchanged.

## Proved and sorry left

Closed one existing hole:
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality`
(node `def-pur-scheme-geometric-frobenius`). The item now has zero `sorry`s.
Added zero holes and split off zero statements. All three new private helpers
are completely proved. The proof uses the existing stated
`AlgebraicGeometry.Scheme.proEtaleFactorizedPullback_pasting`
(node `lem-pur-factorized-pullback-square-pasting`), whose existing hole is unchanged.
This is a proof from declared dependencies, not a claim that the transitive
axiom closure is already sorry-free.

## No longer needed

Removed redundant private imports:

- `Sheaf.AlgebraicGeometry.ProEtaleCanonicalPullbackComposition`
- `Mathlib.AlgebraicGeometry.Pullbacks`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius`
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`

Their required declarations are already available through retained public dependencies.
The planned dependency `lem-pur-unrestricted-frobenius-factorization`
(`Sheaf.AlgebraicGeometry.UnrestrictedFrobeniusFactorization`) is not used: the
item already proves the necessary factorization directly by the pullback projections
and naturality of powers, and proves the scheme-square identity by base change.
Removed that dependency from the proof route. No module is withdrawn and no source-library
declaration is removed. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The DAG still asked this module to invoke the separate unrestricted-factorization
node even though its existing Lean proof already establishes those identities directly.
The naturality step also needed an explicit identification of the two normalized
compositor choices; the adjunction-unit calculation supplies it without changing
any construction or choosing an unspecified comparison. No statement is disputed.
The argument uses no nonemptiness, absolute finite-type, or Cartesian assertion for
the scheme-Frobenius square. Equality elimination and naturality also cover identity
arrows, empty schemes, and the zero coefficient ring.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
