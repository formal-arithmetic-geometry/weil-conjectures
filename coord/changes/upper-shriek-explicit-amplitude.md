# Explicit-amplitude bounded-below upper shriek interface

## Reason

The returned delivery's Sheaf alias restated the source theorem word for word. This repair
replaces that alias with a genuinely more general coefficient-category theorem, proved directly
from the adjunction and t-structure orthogonality, while preserving the adopted source API.

## Old

`Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow` declared
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriekWithAmplitude` only for finite commutative
ModuleCat coefficients and delegated verbatim to
`AlgebraicGeometry.Etale.hasBoundedBelowUpperShriek_of_amplitude`. The declaration duplicated
an existing source statement and was rejected by `import_prune_check.py`.

## New

The Sheaf module now proves `hasBoundedBelowUpperShriekWithAmplitude` for an arbitrary
Grothendieck-abelian coefficient category `A`, assuming `(R(f)_![A]).IsLeftAdjoint` and an
explicit upper-amplitude bound. Its proof is the complete adjunction and t-structure
orthogonality argument, so the result strictly generalizes the finite ModuleCat theorem.
The adopted source item keeps its existing public signatures. Its explicit-amplitude theorem
has only a proof-preserving `simpa` normalization, and the composition implementation drops
two unused section variables without changing public declarations.

## Users

| module | holder | effect |
|---|---|---|
| `Sheaf.SixFunctors.Etale.Derived.UpperShriekBoundedBelow` | C4 | General interface, no duplicate source statement. |
| `WeilConjectures.SixFunctors.Etale.Derived.UpperShriek` | C4 | Existing source API retained; proof normalization only. |
| `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekComposition` | unclaimed | Unused section variables removed; theorem signatures unchanged. |

## Status

landed 20261017T155211-L-1645319 2026-10-17 (merge of deliver/C4/WeilConjectures.SixFunctors.Etale.Derived.UpperShriek)
ready for landing.
