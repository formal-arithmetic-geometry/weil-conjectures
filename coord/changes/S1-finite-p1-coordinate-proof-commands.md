# AlgebraicGeometry.Etale.finiteP1CoordinateKernel

## Reason

The explicit private coordinate-isomorphism construction uses pullbacks and the
total-degree grading of the polynomial ring. Open CategoryTheory.Limits and
activate MvPolynomial.gradedAlgebra locally while elaborating the item.
The interface checker conservatively records these elaboration commands.
All existing signatures, attributes, definitions and public imports remain
unchanged. The new helpers are private and proved or explicitly constructed;
their irreducibility attribute applies only to the new private isomorphism.

## Old

```lean
open CategoryTheory
```

There was no local grading registration or private helper declaration.

## New

```lean
open CategoryTheory CategoryTheory.Limits
```

Inside the existing namespace:

```lean
attribute [local instance] MvPolynomial.gradedAlgebra
```

The explicit private graded renaming, inverse Proj maps, base-changed
isomorphism and over-base equation implement the existing docstring's coordinate
construction. A private conjugate_identity lemma cancels an isomorphism around
the functorial image of an identity. These additions change no public data.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SmoothPurity.FiniteP1AdjunctionOfIntegrals | unclaimed | Applies the unchanged theorem with exactly the same arguments; local namespace opening and grading registration do not change its elaboration environment. |

This is the only direct Lean importer. There is no forced adaptation and no
change to a definition used by a target.

## Status

landed 20261026T082918-L-2236171 2026-10-26 (merge of deliver/S1/Sheaf.SmoothPurity.FiniteP1CoordinateKernel)
