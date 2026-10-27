# AlgebraicGeometry.SupportedConstantNormalization.exchange

## Reason

Factor the pro-etale adjunction transpose through the generic data definition
`closedTranspose`, following the existing `openTranspose` interface. Unfolding
the helper gives the original formula verbatim. No object, morphism, choice,
normalization, hypothesis or universe changes. The purpose is to avoid kernel
conversion timeouts when specializing the generic mate identity to constant
module sheaves. No compilation limit is changed. This definition is reached
by target statements; their meanings remain definitionally identical, and
the repair is flagged for independent statement review.

## Old

```lean
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (constant A false Z) ≫ (Etale.lowerStar (ModuleCat.{u + 1} A) i').map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
          (ModuleCat.of A A)).hom
  | true => (adj A true i').homEquiv _ _
      ((square A true sq).hom.app (supported A true i) ≫
        (pull A true g).map ((adj A true i).counit.app (constant A true Z)) ≫
        (unitIso A true g).hom)
```

## New

```lean
def closedTranspose
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {r : C ⥤ D} {s : D ⥤ C} {r' : C' ⥤ D'} {s' : D' ⥤ C'}
    (a : r ⊣ s) (a' : r' ⊣ s') (L : C ⥤ C') (Q : D ⥤ D')
    (t : L ⋙ r' ≅ r ⋙ Q) (d : D) {d' : D'} (q : Q.obj d ⟶ d') :
    L.obj (s.obj d) ⟶ s'.obj d' :=
  a'.homEquiv _ _ (t.hom.app (s.obj d) ≫ Q.map (a.counit.app d) ≫ q)

/-- The canonical closed exchange, defined by its actual adjunction mate.
Source: Stacks 03S6, 095L; Milne, Section 9
(blueprint: lem-pur-supported-constant-exchange-normalization). -/
def exchange (pro : Bool) {Z' Z X' X : Scheme.{u}}
    {g : Z' ⟶ Z} {i' : Z' ⟶ X'} {i : Z ⟶ X} {h : X' ⟶ X}
    (sq : ChosenCartesianSquare g i' i h) :
    (pull A pro h).obj (supported A pro i) ⟶ supported A pro i' :=
  match pro with
  | false => (Etale.baseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
      (constant A false Z) ≫ (Etale.lowerStar (ModuleCat.{u + 1} A) i').map
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
          (ModuleCat.of A A)).hom
  | true => closedTranspose (adj A true i) (adj A true i')
      (pull A true h) (pull A true g) (square A true sq)
      (constant A true Z) (unitIso A true g).hom
```

## Users

The source scan `tools/downstream.py ... --uses exchange` reports nine explicit
users. All 134 current transitive import consumers retain the same public signatures
and definitionally equal exchange. No consumer source adaptation is required. The repaired normalization file
compiled in 30.9 seconds. Its private `normalized_closed_exchange` and
`exchange_mate` interfaces now retain the transpose name, and a proved generic
`normalized_closed_transpose` wrapper supplies its normalization equation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SupportedConstantExchangeNormalization | unclaimed | Same exchange; no adaptation. |
| Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison | J5 | Same exchange; native section API. |
| Sheaf.Paper.ClosedSupportExceptionalMate | unclaimed | Same exchange; no adaptation. |
| Sheaf.Paper.LineZeroClassExchange | unclaimed | Same exchange; no adaptation. |
| Sheaf.Paper.SectionCompactSourceExchange | H7 | Same exchange; no adaptation. |
| Sheaf.Paper.SectionCompactSourceMaps | unclaimed | Same exchange; no adaptation. |
| Sheaf.Paper.SectionSupportedProExchangeIso | unclaimed | Same exchange; no adaptation. |
| Sheaf.Paper.SupportedCartierDerivedPullback | unclaimed | Same exchange; no adaptation. |
| Sheaf.Paper.SupportedHomPullback | unclaimed | Same exchange; no adaptation. |

## Status

landed 20261026T001858-L-37735 2026-10-26 (merge of deliver/J5/Sheaf.AlgebraicGeometry.ClosedSourceSiteTensorComparison)
