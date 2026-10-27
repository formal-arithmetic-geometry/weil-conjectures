# AlgebraicGeometry.SupportedConstantNormalization.openBackward

## Reason

Factor the displayed adjunction transpose through the generic public data
construction `openTranspose`. The formula is verbatim the old formula with
its adjunctions, functors, square and constant isomorphism as parameters.
Unfolding this single new definition gives the original body definitionally.
The signatures, morphism, normalization, universes and target meanings are
unchanged. There is no choice of a map from an existence theorem.

This repairs a kernel-conversion timeout: specializing a proved pro-etale
mate calculation to the old expanded body exceeded 60 seconds. Keeping the
same construction named across the generic theorem and its specialization
checks the open invertibility argument in 6.9 seconds, also at a reduced
10000-heartbeat diagnostic limit. No timeout or heartbeat limit is raised.

## Old

```lean
def openBackward (pro : Bool) {U' U X' X : Scheme.{u}}
    {g : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) :
    (shriek A pro j').obj (constant A pro U') ⟶
      (pull A pro h).obj ((shriek A pro j).obj (constant A pro U)) :=
  ((openAdj A pro j').homEquiv _ _).symm
    ((unitIso A pro g).inv ≫
      (pull A pro g).map ((openAdj A pro j).unit.app (constant A pro U)) ≫
      (square A pro sq).inv.app ((shriek A pro j).obj (constant A pro U)))
```

## New

```lean
def openTranspose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : s ⊣ r) (a' : s' ⊣ r') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) {d : D} {d' : D'} (q : Q.obj d ≅ d') :
    s'.obj d' ⟶ L.obj (s.obj d) :=
  (a'.homEquiv _ _).symm
    (q.inv ≫ Q.map (a.unit.app d) ≫ t.inv.app (s.obj d))

def openBackward (pro : Bool) {U' U X' X : Scheme.{u}}
    {g : U' ⟶ U} {j' : U' ⟶ X'} {j : U ⟶ X} {h : X' ⟶ X}
    [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : ChosenCartesianSquare g j' j h) :
    (shriek A pro j').obj (constant A pro U') ⟶
      (pull A pro h).obj ((shriek A pro j).obj (constant A pro U)) :=
  openTranspose (openAdj A pro j) (openAdj A pro j')
    (pull A pro h) (pull A pro g) (square A pro sq) (unitIso A pro g)
```

## Users

`tools/downstream.py --uses` finds only the item itself as an explicit user of
`openBackward`. All 66 transitive import consumers see the same definitionally
equal morphism and the same public signatures; no adaptation is required.
The new helper is attached to the existing normalization node's Lean record.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | T3 | The same transpose, factored through a generic data definition. |

The independent statement review can unfold `openTranspose` once to check
that every target reaching this construction retains its original meaning.

## Status

landed 20261024T191216-L-272422 2026-10-24 (merge of deliver/T3/Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization)
