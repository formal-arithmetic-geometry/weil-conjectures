/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.DerivedInternalHom
import Sheaf.Algebra.Homology.HomComplex
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom

/-! # Derived internal Hom from the structure sheaf

Source: Stacks Project, sites-cohomology.tex, Section 08J7.
-/

@[expose] public section

universe u wY

open CategoryTheory Opposite AlgebraicGeometry

namespace AlgebraicGeometry

/-- Internal Hom from the degree-zero structure sheaf is the identity on the derived
category, naturally in every unbounded derived object.

Source: Stacks Project, sites-cohomology.tex, Section 08J7; duality.tex, Tag 0AX3.
(blueprint: lem-sc-derived-internal-hom-unit-iso).

Proof:
1. On every open and in every degree, evaluation at one identifies
   Hom(O_Y, I^n) with I^n. Its inverse sends a section x to r -> r*x; linearity
   gives both inverse identities. These maps commute with restrictions.
2. In Hom^bullet(O_Y[0], I), only the degree-zero term of the first argument
   contributes. The previous maps identify the differential with that of I,
   hence give a chain isomorphism natural in I.
3. Use derivedInternalHom_comparison with the functorial K-injective replacement.
   Compose the chain isomorphism with the inverse of Q of the resolution map.
   Naturality gives an isomorphism after precomposition by Q.
4. Fully faithful precomposition by the localization Q descends this to the
   displayed natural isomorphism. All degrees are handled independently, so no
   boundedness hypothesis is needed. -/
theorem derivedInternalHom_unit_iso (Y : Scheme.{u})
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    Nonempty ((Functor.curry.obj
        (derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf)).obj
          (op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              (SheafOfModules.unit Y.ringCatSheaf))) ≅ 𝟭 _) := by
  sorry

end AlgebraicGeometry
