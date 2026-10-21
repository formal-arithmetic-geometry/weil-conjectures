/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.ExactCompactificationUnit
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons

/-!
# Compatibility of exact compactification units with refinements

Source: Stacks Project, Tags 0F7B, 0F7I and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-refinement).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Two compactification units with the same underlying sheaf inclusion agree under the
canonical common-refinement comparison.
Source: Stacks Project, Tags 0F7B, 0F7I and 0D6E
(blueprint: lem-sfb-exact-compactification-unit-refinement).

Proof: first take a proper refinement from c to d. Its comparison is the proper/open
comparison for the coarser open immersion, followed by derived composition of direct images.
The sheaf proper/open map preserves the section in the ordinary direct image. Thus its
composite with the supplied sheaf isomorphism for d is the supplied isomorphism for c:
the compactification inclusion is injective, so it cancels. Apply the normalization of the
proper/open comparison on a K-injective resolution of the finer extension by zero. Direct
image preserves K-injectives, and the derived-composition unit identity identifies the two
resolution maps. This is equality of the descended units on homotopy representatives, hence
on the derived category by localization full faithfulness. For arbitrary c and d apply the
refinement identity to their two arrows from the common refinement and cancel the invertible
comparison. This is exactly the definition of the common-refinement comparison used here. -/
theorem exactCompactificationUnit_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (c d : Compactification f)
    (a : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i ⋙
      lowerStar (ModuleCat.{u + 1} A) c.g)
    (b : F ≅ openImmersionLowerShriek (ModuleCat.{u + 1} A) d.i ⋙
      lowerStar (ModuleCat.{u + 1} A) d.g)
    (hab : a.hom ≫ compactificationSheafToDirectImage A c =
      b.hom ≫ compactificationSheafToDirectImage A d) :
    exactCompactificationUnit A c F a ≫
      (rightDerivedLowerShriekOfCompactificationIso A c d).hom =
        exactCompactificationUnit A d F b := by sorry

end AlgebraicGeometry.Etale
