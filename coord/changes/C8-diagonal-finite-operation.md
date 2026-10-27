# AlgebraicGeometry.ProEtale.DiagonalTrace.diagonalTrace_finiteAdjunction_geometric

## Reason

STATEMENT-DISPUTED: the old assertion prescribed the values of an arbitrary function
on all geometric classes from its values on supported diagonal classes. These
classes do not exhaust the inputs. Over an algebraically closed field of
characteristic different from l, the two ruling classes generate
H²(P¹ × P¹, Z/l^(n+1)(1)), while diagonal-supported classes span their sum.
Changing a function on a ruling class preserves the supported equations.

The source constructs the operation by direct image. This repair constructs it
explicitly from the completed coefficient unit and normalized evaluation square,
then proves its geometric equation by naturality. The parent existential theorem
retains its full statement, including both equations for the same operation.
No target statement or existing definition used by a target changes.

## Old

```lean
theorem diagonalTrace_finiteAdjunction_geometric
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (a : SupportedSource l Y f p.Rc) (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
    let VX := p.restrictionX.F.mapDerivedCategory
    let VS := p.restrictionS.F.mapDerivedCategory
    let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
    ∀ (Φ : (UX.obj (completedUnit l (diagonalSurface Y)) ⟶
        evX.obj (VX.obj line)) →
        ((diagonalCompletedUnderlying l (ProjectiveLine Y)).obj
          (completedUnit l (ProjectiveLine Y)) ⟶
            evS.obj (VS.obj ((SpTowerShriek.push l E p.base p.model.geometry).obj line)))),
      (∀ γ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y,
        Φ (UX.map
            ((DerivedCategory.singleFunctor (DiagonalCompleted l (diagonalSurface Y)) 0).map
              (completedSupportedUnit l Y) ≫ γ) ≫
          shiftedComparison UX (VX ⋙ p.LX.R) (p.coefficientsX.lineMap l E p.LX) 2 ≫
            (p.LX.projection n).app _) =
          (diagonalCompletedUnderlying l (ProjectiveLine Y)).map
              (a.hom ≫ p.Rc.R.map γ) ≫ p.sourceMap l E ≫
            (p.LS.projection n).app _ ≫ evS.map (p.varying.inv.app _)) →
      ∀ θ : SpTowerClasses.unit (diagonalSurface Y)
          (SpTowerClasses.Arings l E (diagonalSurface Y)) ⟶ line,
        Φ ((p.coefficientsX.unitMap l E p.LX ≫ (p.LX.projection n).app _) ≫
          evX.map (VX.map θ)) =
          (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
            evS.map (VS.map
              ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
                ((p.model.coefficientPullback.derivedIso l E).hom ≫ θ)))
```

## New

```lean
theorem diagonalTrace_finiteAdjunction_geometric
    (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    [DiagonalTraceLocalizations l (ProjectiveLine Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    (f : diagonalSurface Y ⟶ ProjectiveLine Y)
    (p : Presentation l (ULift.{u} (Padic l)) f)
    (n : ℕ) :
    let E := ULift.{u} (Padic l)
    let UX := diagonalCompletedUnderlying l (diagonalSurface Y)
    let VX := p.restrictionX.F.mapDerivedCategory
    let VS := p.restrictionS.F.mapDerivedCategory
    let evX := ((evaluation ℕᵒᵖ (DiagonalMod l (diagonalSurface Y))).obj
      (op n)).mapDerivedCategory
    let evS := ((evaluation ℕᵒᵖ (DiagonalMod l (ProjectiveLine Y))).obj
      (op n)).mapDerivedCategory
    let line := (SpTowerClasses.line l E p.chernX)⟦(2 : ℤ)⟧
    let Φ := fun η : UX.obj (completedUnit l (diagonalSurface Y)) ⟶
        evX.obj (VX.obj line) ↦
      p.finitePushUnit l ≫ p.Rf.R.map η ≫ (p.finitePushComparison l n).hom.app line
    ∀ θ : SpTowerClasses.unit (diagonalSurface Y)
          (SpTowerClasses.Arings l E (diagonalSurface Y)) ⟶ line,
        Φ ((p.coefficientsX.unitMap l E p.LX ≫ (p.LX.projection n).app _) ≫
          evX.map (VX.map θ)) =
          (p.coefficientsS.unitMap l E p.LS ≫ (p.LS.projection n).app _) ≫
            evS.map (VS.map
              ((SpTowerShriek.adjunction l E p.base p.model.geometry).homEquiv _ _
                ((p.model.coefficientPullback.derivedIso l E).hom ≫ θ)))
```

## Users

`tools/downstream.py Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric --uses
diagonalTrace_finiteAdjunction_geometric` found only the assigned module and
its parent as declaration users. The direct importer is that parent.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric | C8 | Correct the false arbitrary-function interface; prove the canonical-operation equation. |
| Sheaf.Paper.DiagonalTraceFiniteAdjunctionFactorization | unclaimed | Statement verbatim; construct the explicit common witness and use its supported and geometric equations. |

The direct importer of the parent is
`Sheaf.Paper.DiagonalTraceFiniteDivisorAdjoint`; its original statement and proof
continue to use the parent unchanged. It is checked against this overlay.
The supported-half module held by C9 is untouched.

## Status

landed 20261027T205852-L-1626047 2026-10-27 (merge of deliver/C8/Sheaf.Paper.DiagonalTraceFiniteAdjunctionGeometric)
