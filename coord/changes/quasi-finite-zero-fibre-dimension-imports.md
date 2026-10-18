# Algebra.isQuasiFiniteAtPrime_iff_topologicalKrullDimAt_eq_zero

## Reason

The complete proof uses the existing topological zero-dimensional finiteness theorem,
so it no longer needs the scheme API or the retired quasi-finiteness re-export module.
The theorem's complete signature, universes and visibility are unchanged. Only public
import exports are pruned; no definitions or target meanings change.

## Old

```lean
public import Sheaf.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Scheme
```

## New

```lean
public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
```

The retired Sheaf module only publicly imports the source module now imported directly.
The sole direct consumer is `Sheaf.AlgebraicGeometry.DescendQuasiFiniteAffine`;
it already imports the scheme API independently through its own public imports
of `Mathlib.AlgebraicGeometry.Pullbacks` and `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`.
It is compiled unchanged against the new module. Every other downstream module reaches
this item through that direct consumer, and no public declaration signature changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ConstantShriekRelativeDimensionOne | H5 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.DescendQuasiFiniteAffine | P7 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleAffineLineShriekSheafConstructible | U2 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleCompactificationConstructibility | M3 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness | C6 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible | C9 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.LisseOpenRelativeLineConstructibility | D9 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.ProperSmoothCurvesFiniteModule | R5 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QuasiFiniteAffineEtaleThickeningDecomposition | J7 | No declaration or definition changes; no adaptation needed. |
| Sheaf.AlgebraicGeometry.QuasiFiniteShriekConstructible | W3 | No declaration or definition changes; no adaptation needed. |

## Status

landed 20261018T062929-L-685305 2026-10-18 (merge of deliver/U8/Sheaf.RingTheory.QuasiFiniteAtPrimeZeroFibreDimension)
