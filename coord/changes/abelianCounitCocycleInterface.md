# abelianPushforward and abelianAdjunction

## Reason

The independent cocycle statement needs the fixed-site abelian pushforward and its adjunction.
Keeping these declarations only in the upper calculation module would create an import cycle.
Move their unchanged declarations into AbelianCounitCocycleCalculation, and publicly import
that module from AbelianCounitResolutionCalculation. The full names, universes, visibility,
statements and definition bodies are identical. No target definition changes its meaning.

## Old

Declared in Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation:

```lean
/-- Abelian direct image, with the site categories fixed before instance search.
Source: Stacks, Tag 01F7. -/
abbrev abelianPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base

/-- The inverse-image/direct-image adjunction on the fixed site categories.
Source: Stacks, Tag 01F7. -/
def abelianAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y) :
    invImage f ⊣ abelianPushforward f :=
  TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base

```

## New

The exact declarations above are in Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation.
The original module reexports them with:

```lean
public import Sheaf.AlgebraicGeometry.AbelianCounitCocycleCalculation
```

The new module constructs abelianInjectiveResolutionIso by composing the terminal-source Ext
isomorphism, siteSectionsObjIso, and rightDerivedObjIsoOfResolution for the supplied abelian
injective resolution. The definition uses the explicit SheafOfModules category of moduleRings, which is
definitionally the scheme module category. It is irreducible. This is a concrete composition of
canonical isomorphisms.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation | G2 | Uses the same declarations through its public import; no existing signature changes. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopies | unclaimed | Imports the original module; same declarations remain exported; no adaptation. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCore | unclaimed | Imports the original module; same declarations remain exported; no adaptation. |
| Sheaf.AlgebraicGeometry.AbelianReplacementSectionHomotopiesCoreParts | unclaimed | Imports the original module; same declarations remain exported; no adaptation. |

The downstream --uses searches for abelianPushforward and abelianAdjunction find the item and AbelianReplacementSectionHomotopiesCoreParts as actual identifier
users. Both retain the same exported declarations. No other module needs an edit. The generic
acyclicComparison_naturality is used as a tool from another unit; its statement concerns
arbitrary abelian categories, so this does not bypass the unit route.

## Status

landed 20261014T085851-L-233567 2026-10-14 (merge of deliver/G2/Sheaf.AlgebraicGeometry.AbelianCounitResolutionCalculation)
