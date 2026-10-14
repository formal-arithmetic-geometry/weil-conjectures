# AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution.abelianEdgeHom

## Reason

Name the inverse-image/counit composite in the standard-source calculation module,
then retain abelianEdgeHom as a definitionally equal alias with its exact signature.
The expanded composite causes expensive kernel reduction when repeated inside the
standard-source statement. The named morphism has an explicit source and target and
lets the statement reuse its checked type. This does not change the cohomology map,
its additive structures, or any target meaning. The new module is publicly imported
because the alias definition uses it.

## Old

```lean
def abelianEdgeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    AddCommGrpCat.of (H ((pushforward f).obj F) p) ⟶ AddCommGrpCat.of (H F p) :=
  AddCommGrpCat.ofHom ((Sheaf.H.map (coeff f (𝟙 ((pushforward f).obj F))) p).comp
    (Sheaf.H.mapFunctor (invImage f) (constIso f).symm
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((pushforward f).obj F)) p))
```

## New

```lean
abbrev abelianEdgeHom {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    AddCommGrpCat.of (H ((pushforward f).obj F) p) ⟶ AddCommGrpCat.of (H F p) :=
  standardSectionExtHom f F p
```

standardSectionExtHom has exactly the old defining body and exactly the old type.
Thus unfolding the alias and standardSectionExtHom recovers the original expression.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionDiagram | D3 | Alias with identical type and value; local proofs use standard calculation. |
| Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionEdge | unclaimed at this checkout | No edit required: all referenced declarations retain their types and definitional meanings. |

These are the two modules listed by tools/downstream.py with --uses abelianEdgeHom.
All 372 transitively importing modules retain the same statements and definitions:
the only existing definition changed is replaced by a definitionally equal term.
No adaptation is made and no target needs a semantic re-review for this alias.

## Status

landed 20261014T030642-L-342139 2026-10-14 (merge of deliver/D3/Sheaf.AlgebraicGeometry.ModuleCohomologyExtSectionDiagram)
