# AlgebraicGeometry.ProEtale.SpTowerClasses.FiniteDiagonalNormalization

## Reason

The original nested application spends 45--54 seconds in kernel type checking of this
single definition, bringing the proved item above the 60-second limit. Share the four
argument expressions through local let bindings, as the neighbouring
`FiniteChernNormalization` already does. The evaluated arrow is now reused through the
existing `evaluatedDiagonal` definition.
The new `singleBoundaryEquality` forms single complexes and the root shift before specializing
the coefficient objects. Zeta reduction and unfolding it, `evaluatedDiagonal` and
`forgetEvaluatedArrow` give identical bodies; every hypothesis, arrow, endpoint, sign and comparison is unchanged.
The public type and all existing declarations are preserved. The local irreducibility
annotations affect only elaboration in this module, not importers.

## Old

```lean
def FiniteDiagonalNormalization {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) : Prop :=
  ∀ n : ℕ,
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        (finiteSupportedQuotient l E d.geometry n))
      (((DerivedCategory.singleFunctor (DiagonalAb (diagonalSurface S)) 0).map
        (finiteRootMap l E (diagonalSurface S) n))⟦(2 : ℤ)⟧')
      (forgetEvaluatedArrow (SpTowerShriek.ev l E (diagonalSurface S) n)
        (finiteForget l E (diagonalSurface S) n) (lineEvaluation l E c n)
        ((d.geometry.push.singleFunctorCompRightDerivedFunctorIso).inv.app _ ≫
          diagonalArrow l E c d.sourceIso))
      (mapSingleArrow (abEvaluation (diagonalSurface S) n) (2 : ℤ)
        (kummerComposite
          (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
          c.kummer.exact (diagonalBoundary S)))
```

## New

```lean
def FiniteDiagonalNormalization {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) : Prop :=
  ∀ n : ℕ,
    let quotient := finiteSupportedQuotient l E d.geometry n
    let roots := finiteRootMap l E (diagonalSurface S) n
    let arrow := mapSingleArrow (finiteForget l E (diagonalSurface S) n) (2 : ℤ)
      (evaluatedDiagonal l E d n)
    let boundary := mapSingleArrow (abEvaluation (diagonalSurface S) n) (2 : ℤ)
      (kummerComposite
        (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
        c.kummer.exact (diagonalBoundary S))
    singleBoundaryEquality quotient roots arrow boundary
```

The item additionally publicly imports `Sheaf.Paper.SingleBoundaryNormalization` because
its definition body uses this generic predicate. The existing public import stays verbatim.
The new helper has a real body, uses `finiteBoundaryEquality`, and introduces no hole.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.TowerClassFiniteDiagonal | G7 | Two theorem holes closed; normalization arguments shared without changing the predicate. |
| Sheaf.Paper.SmoothPurityTowerClasses | unclaimed (no current claim record) | Definitionally unchanged predicate; original importer compiled cleanly against this packet. |

No other existing module imports the item or mentions this predicate. No consumer
adaptation is required: the refactoring shares arguments, forms single/shift witnesses
before specialization, and reuses the definitionally equal evaluated arrow.

Validation: `lcompile.py --all` accepted the five delivery modules and the unchanged direct
importer `Sheaf.Paper.SmoothPurityTowerClasses` (exit 0, no errors or warnings). The unchanged
consumer copy was removed from the packet after compilation. No adaptation was needed.

## Status

landed 20261027T112353-L-1576509 2026-10-27 (merge of deliver/G7/Sheaf.Paper.TowerClassFiniteDiagonal)
