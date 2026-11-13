/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward
import WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberBackward

/-!
# The fibre of a strict henselization over its distinguished point

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 04GW](https://stacks.math.columbia.edu/tag/04GW)
* [Stacks Project, Tag 04GP](https://stacks.math.columbia.edu/tag/04GP)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The only point of the strict henselization over the underlying geometric point is
its closed point, in any local affine presentation. -/
theorem strictHenselizationStructuralMap_fiber_eq_closedPoint
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω]
    [CommRing A] [IsLocalRing A]
    (s : Spec (.of Ω) ⟶ S) (e : Spec (.of A) ≅ strictLocalization s)
    (x : Spec (.of A)) :
    (e.hom ≫ strictLocalizationToBase s) x = s (IsLocalRing.closedPoint Ω) ↔
      x = IsLocalRing.closedPoint A := by
  constructor
  · exact strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq s e x
  · intro hx
    subst x
    exact strictHenselizationStructuralMap_closedPoint_eq s e

end AlgebraicGeometry.Scheme
