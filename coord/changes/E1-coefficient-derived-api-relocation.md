# Cached coefficient derived functor interfaces

## Reason

The second reader removed an equivalent restatement of the entire item. The two
independent geometric statements need the existing cached derived-functor interfaces,
without importing the theorem that will use them. Elaborating raw concrete derived
functors exceeded the heartbeat limit. Move the existing generic cached definitions
verbatim to `Sheaf.Paper.CoefficientDerivedFunctorAPI`, publicly imported by the item.
The API and its users share the named local proof instance
`coefficientProfiniteEssentiallySmall`. Its body is the same
`essentiallySmallSelf.{0} _` as before; this avoids repeated type comparison through
large derived category constructions built using different anonymous instance names.
This breaks the potential import cycle and preserves all existing names, signatures,
attributes, definition bodies and downstream meanings. No target statement or definition
body changes. The new API node records this existing construction, rather than creating
a second definition of any notion.

## Old

In `Sheaf.Paper.FiniteDiscreteDerivedCoefficientData`:

```lean
section DerivedFunctorAPI

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] {S T : Scheme.{u}} (h : S ⟶ T)

/-- The derived pullback with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedUpperStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) :=
  L((h)^*⟦Λ⟧)

/-- The derived pushforward with its derivability instances fixed at a generic coefficient ring. -/
noncomputable def coefficientDerivedLowerStar :
    DerivedCategory (Mod (Sheaf (ProEt.topology S) Ab.{u + 1}) (condensedRingObj Λ S)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)) :=
  R((h)_*⟦Λ⟧)

/-- The derived coefficient adjunction, with the cached derived functor interfaces. -/
@[irreducible] noncomputable def coefficientDerivedAdjunction :
    coefficientDerivedUpperStar Λ h ⊣ coefficientDerivedLowerStar Λ h :=
  derivedUpperStarLowerStarAdjunction Λ h

end DerivedFunctorAPI

/-- The ambient derived pullback comparison, before restricting to constructible objects. -/
@[irreducible] noncomputable def coefficientAmbientSquare
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' f' f g) :
    coefficientDerivedUpperStar Λ g ⋙
        coefficientDerivedUpperStar Λ f' ≅
      coefficientDerivedUpperStar Λ f ⋙
        coefficientDerivedUpperStar Λ g' :=
  (leftDerivedUpperStarComp Λ f' g).symm ≪≫
    eqToIso (by rw [← sq.w]) ≪≫
    leftDerivedUpperStarComp Λ g' f
```

## New

The exact same four declarations above, with the same namespaces and variables, are
now in `Sheaf.Paper.CoefficientDerivedFunctorAPI`. The item retains its original public
encoding import and adds:

```lean
public import Sheaf.Paper.CoefficientDerivedFunctorAPI
```

The new API additionally declares `CoefficientCoherentPullbackData` and its
`FiniteDiscreteCoherentPullbacks` abbreviation. This is a genuine sub-interface with
only the original pullback and square fields, omitting right-mate invertibility. It
is a record type; no data is chosen from an unproved theorem.

New, strictly smaller geometric statements are in their own modules, imported privately
by the proof of the original theorem. No existing public declaration is removed from
the importer-visible interface. The four moved declarations are exported transitively.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.FiniteDiscreteDerivedCoefficientData | E1 | Definitions re-exported unchanged; theorem proof replaced by a genuine decomposition. |
| Sheaf.Paper.CoefficientExchangeFromComparisons | C3 | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.Paper.FiniteDiscreteCoefficientExchange | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeComparison | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.Paper.FiniteDiscreteExchangeRealization | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| TargetsCheck | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same re-exported definitions and theorem statement; no semantic change or source adaptation. |

`tools/downstream.py --uses` for the four moved names finds only the item itself;
all ten transitive downstream modules are also listed above. No foreign-held module
is edited. In particular, `Challenge.lean` is untouched, and no definition body used
by a target changes; relocation does not reopen the statement's mathematical review.

## Status

landed 20261016T131233-L-3106244 2026-10-16 (merge of deliver/E1/Sheaf.Paper.FiniteDiscreteDerivedCoefficientData)
