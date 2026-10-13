module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
namespace AlgebraicGeometry

/-- Shifted-unit comparison needed for the K-flat counit data.

Source: Stacks Project, Tag 06YJ, translated-unit comparison.  The proof uses
that a monoidal derived pullback carries the monoidal unit to the monoidal unit,
and that a triangulated functor carries the integer shift of an object to the
corresponding shift of its image.  Composing these canonical isomorphisms with
the canonical shifted-unit comparison on the target gives the displayed
isomorphism; the required coherence follows from the functoriality of the
shift and the monoidal unitors.
(blueprint: lem-sc-derived-pullback-shifted-unit-iso-data).
-/
theorem exists_derivedPullback_shifted_unit_iso
    {Z Y : Scheme.{u}} [IsNoetherian Z] [IsNoetherian Y] (f : Z ⟶ Y) [IsProper f]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [Functor.Monoidal (derivedPullback f)] :
    Nonempty ((derivedPullback f).obj ((𝟙_ (schemeDerivedCategory Y))⟦(1 : ℤ)⟧) ≅
        (𝟙_ (schemeDerivedCategory Z))⟦(1 : ℤ)⟧) := by
  sorry

end AlgebraicGeometry
