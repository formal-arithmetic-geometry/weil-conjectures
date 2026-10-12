module

public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The module direct image along a closed immersion preserves homology of short complexes.
Source: Stacks Tags 00AE and 01AX.
(blueprint: lem-sc-closed-immersion-algebra-direct-image-preserves-homology)
-/
theorem closedImmersion_algebraDirectImage_preservesHomology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).PreservesHomology := by
  sorry

end AlgebraicGeometry
