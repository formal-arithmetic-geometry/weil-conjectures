# WeilConjectures.projectionTensorCoordinateComponent_tensorAction

## Reason

The assigned module exceeded its per-file compile limit. A generic categorical
expansion preserves the existing private tensor-action equation, and separating this
self-contained calculation distributes work out of the four-stage module. Focused
profiling later identified the larger remaining kernel cost as the neighboring
`fixedComponent_eq`; no kernel timing is attributed to the tensor-action helper. Move the proved equation to its own
module after that local proof simplification. No new hole is introduced.

## Old

The assigned module's private helper was:

```lean
private theorem genericProjection_tensorAction
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (k : DerivedCategory (Sheaf (ProEt.topology X) A))
    (q N : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    let T := derivedTensor A X
    let U := (upperStar A f).leftDerivedFunctor
    let F := rightDerivedLowerShriekOfCompactification A c
    ((derivedTensor A Y).flip.obj N).map (projectionTensorCoordinateComponent A c k q) ≫
      projectionTensorCoordinateComponent A c ((T.obj k).obj (U.obj q)) N =
    (projectionActionAssociator A Y (F.obj k) q N).hom ≫
      projectionTensorCoordinateComponent A c k (((derivedTensor A Y).obj q).obj N) ≫
      F.map ((T.obj k).map (leftDerivedUpperStarTensorIso A f q N).hom) ≫
      F.map (projectionActionAssociator A X k (U.obj q) (U.obj N)).inv := by
  dsimp only
  dsimp only [projectionTensorCoordinateComponent]
  have h := genericProjectionAction_compactification A f c k q N
  have hm := (rightDerivedLowerShriekOfCompactification A c).map_comp
    (((derivedTensor A X).obj k).map (leftDerivedUpperStarTensorIso A f q N).hom)
    (projectionActionAssociator A X k
      ((upperStar A f).leftDerivedFunctor.obj q)
      ((upperStar A f).leftDerivedFunctor.obj N)).inv
  exact h.symm.trans (congrArg (fun t ↦
    (projectionActionAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj k) q N).hom ≫
    ((projectionMapOfCompactification A c).app k).app
      (((derivedTensor A Y).obj q).obj N) ≫ t) hm)

```

## New

In `lean/Sheaf/Paper/ProjectionTensorActionExpansion.lean`:

```lean
theorem projectionTensorCoordinateComponent_tensorAction
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [UpperStarPreservesFlat A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (k : DerivedCategory (Sheaf (ProEt.topology X) A))
    (q N : DerivedCategory (Sheaf (ProEt.topology Y) A)) :
    let T := derivedTensor A X
    let U := (upperStar A f).leftDerivedFunctor
    let F := rightDerivedLowerShriekOfCompactification A c
    ((derivedTensor A Y).flip.obj N).map (projectionTensorCoordinateComponent A c k q) ≫
      projectionTensorCoordinateComponent A c ((T.obj k).obj (U.obj q)) N =
    (projectionActionAssociator A Y (F.obj k) q N).hom ≫
      projectionTensorCoordinateComponent A c k (((derivedTensor A Y).obj q).obj N) ≫
      F.map ((T.obj k).map (leftDerivedUpperStarTensorIso A f q N).hom) ≫
      F.map (projectionActionAssociator A X k (U.obj q) (U.obj N)).inv := by
  dsimp only
  dsimp only [projectionTensorCoordinateComponent]
  exact splitProjectionActionImage (rightDerivedLowerShriekOfCompactification A c)
    (projectionActionAssociator A Y
      ((rightDerivedLowerShriekOfCompactification A c).obj k) q N).hom
    (((projectionMapOfCompactification A c).app k).app
      (((derivedTensor A Y).obj q).obj N))
    (((derivedTensor A X).obj k).map (leftDerivedUpperStarTensorIso A f q N).hom)
    (projectionActionAssociator A X k
      ((upperStar A f).leftDerivedFunctor.obj q)
      ((upperStar A f).leftDerivedFunctor.obj N)).inv _
    (genericProjectionAction_compactification A f c k q N)
```

The new module proves the elementary `splitProjectionActionImage` helper first,
then applies the already proved general coefficient-category private library lemma
in `FiniteProjectionActionLaws`. The assigned module calls the new public theorem
instead of its old private helper, and imports the module privately. Its original
public statements, definitions and attributes stay identical.

## Users

The old private name occurs only in the assigned module and its identical
quarantined archive; a current/quarantined direct-import search finds no consumers.
The archive is preserved unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ProjectionFormulaCoherence | J4 | Replaces private helper with the proved public equation; no statement changes. |
| Sheaf.Paper.ProjectionTensorActionExpansion | J4, new | Owns the generic proved equation and elementary rewriting helper. |

## Status

landed 20261026T222721-L-685893 2026-10-26 (merge of deliver/J4/Sheaf.Paper.ProjectionFormulaCoherence)
