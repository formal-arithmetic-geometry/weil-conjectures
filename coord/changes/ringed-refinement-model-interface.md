# SheafOfModules.RingedRefinement.Package

## Reason

Move the unchanged presentation definitions to RingedRefinementModels so that the
new construction/coherence/comparison obligations can import their types without
an import cycle through the theorem they prove. This is a dependency-interface
separation for proof decomposition, not a compile-time workaround. No definition
body, signature, visibility, coefficient convention, or target meaning changes.

## Old

```lean
structure Package (m : Mode) (T : Scheme.{u}) where
  coefficients : Coefficients m T
  operations : Calculus coefficients
  spatial : Spatial operations
  scalars : ScalarComparisons operations
  associators : ScalarComposition operations
  opens : OpenComparisons spatial
  refinements : Refinements opens
  laws : Laws scalars associators refinements
  shifts : Shifts scalars refinements
  shapes : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂),
    Shape u j₁ j₂
```

The declaration and all its supporting definitions were in
Sheaf.Paper.RingedRefinementCoefficientSquare.

## New

```lean
structure Package (m : Mode) (T : Scheme.{u}) where
  coefficients : Coefficients m T
  operations : Calculus coefficients
  spatial : Spatial operations
  scalars : ScalarComparisons operations
  associators : ScalarComposition operations
  opens : OpenComparisons spatial
  refinements : Refinements opens
  laws : Laws scalars associators refinements
  shifts : Shifts scalars refinements
  shapes : ∀ {X Y Z : Over T} (u : Y ⟶ Z) (j₁ : X ⟶ Y) (j₂ : X ⟶ Z)
    [IsProper u.left] [IsOpenImmersion j₁.left] [IsOpenImmersion j₂.left]
    [QuasiCompact j₁.left] [QuasiCompact j₂.left] (_h : j₁ ≫ u = j₂),
    Shape u j₁ j₂
```

The exact same definitions are in Sheaf.Paper.RingedRefinementModels. The original
module publicly imports that module. Every original declaration name and public
import remains available. The new definition node records ownership; no duplicate
notion is introduced. Only the declaration's module location changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RingedRefinementCoefficientSquare | D2 | Publicly reexports the same models; proves its unchanged theorem by assembly. |

`tools/downstream.py Sheaf.Paper.RingedRefinementCoefficientSquare` reports zero
other direct/transitive importers. The Package use search reports only the item
itself. Thus no other existing consumer requires adaptation. New modules are
unclaimed and use the unchanged interface. No target-definition review reopens.

## Status

landed 20261019T112441-L-3941270 2026-10-19 (merge of deliver/D2/Sheaf.Paper.RingedRefinementCoefficientSquare)
