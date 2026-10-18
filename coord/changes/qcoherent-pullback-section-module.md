# AlgebraicGeometry.Scheme.Modules.qcoherentPullbackSection

## Reason

The independent normalized refinement-square module needs the section formula.
Keeping this definition in the item module would create an import cycle. Move it,
with its signature and defining expression unchanged, to
`Sheaf.AlgebraicGeometry.QcoherentPullbackSections`, publicly imported by the item.
This is a source move, not a mathematical change to the section pullback
operation. A new definition node records the relocated formula; the original
node now cites it as a statement dependency. Existing importers continue to see
the same declaration through the same item module.

## Old

In `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`:

```lean
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤
```

## New

In `Sheaf.AlgebraicGeometry.QcoherentPullbackSections`, publicly re-exported
by the original module:

```lean
def qcoherentPullbackSection {X Y : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (G : Y.Modules) (ψ : (tensorPullback g).obj F ⟶ G)
    (U : X.Etale) (V : Y.Etale) (p : V.left ⟶ U.left)
    (h : p ≫ U.hom = V.hom ≫ g) :
    Γ((tensorPullback U.hom).obj F, ⊤) ⟶ Γ((tensorPullback V.hom).obj G, ⊤) :=
  tensorSectionsUnit p ((tensorPullback U.hom).obj F) ≫
    ((tensorSectionsComp p U.hom).hom.app F).app ⊤ ≫
    (eqToHom (congrArg (fun f ↦ (tensorPullback f).obj F) h)).app ⊤ ≫
    ((tensorSectionsComp V.hom g).inv.app F).app ⊤ ≫
    ((tensorPullback V.hom).map ψ).app ⊤
```

## Users

`tools/downstream.py` with `--uses qcoherentPullbackSection` reports the item
module as the only textual user of this declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback | Z7 | Publicly imports the new module; theorem statement unchanged. |

There are eight further import descendants, none requiring adaptation:
`ConstantShriekRelativeDimensionOne`, `EtaleAffineLineShriekSheafConstructible`,
`EtaleCompactificationConstructibility`, `EtaleProperDirectImageFiniteness`,
`LisseOpenRelativeLineConstructibility`, `ProperSmoothCurvesFiniteModule`,
`ProperSmoothCurvesPrimeCoefficients`, and `SmoothCurveEtaleStructureDirectImages`,
all under `Sheaf.AlgebraicGeometry`. Their imports and the declaration's
signature and defining expression are preserved. No target statement or the
meaning of a definition used by a target changes. No module held by another
group is adapted.

## Status

landed 20261018T071246-L-1684153 2026-10-18 (merge of deliver/Z7/Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback)
