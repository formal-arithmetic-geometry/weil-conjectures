/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal

/-! # Sheafification and the localized open-site equivalence
Source: Stacks Project, Tag 01CD, localized-site construction.
(blueprint: lem-sc-localized-open-sheafification).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Sheafification commutes with transport along the localized open-site equivalence.
Source: Stacks Project, Tag 01CD, sheafification step in the localized-site construction.
(blueprint: lem-sc-localized-open-sheafification).

Proof: the inverse open-site equivalence identifies presheaves of modules, using
restriction of the structure sheaf for the coefficient rings. Its inverse is
precomposition with the forward site equivalence, with unit and counit supplied
by those of the site equivalence. Covering sieves correspond, so transport
preserves and reflects the sheaf condition. Consequently both displayed
composites are left adjoint to inverse transport followed by forgetting the
sheaf condition: compose the presheaf transport adjunction and the sheafification
adjunction on one side, and the sheafification adjunction and overEquiv adjunction
on the other. Their right adjoints identify by the sectionwise definition of
pushforward. Uniqueness of left adjoints gives the displayed natural isomorphism.
This does not use tensor products, and applies to empty opens and zero rings. -/
theorem exists_localizedOpen_sheafification_iso (X : Scheme.{u}) (U : X.Opens) :
    Nonempty (
      PresheafOfModules.sheafification.{u}
          (R := (moduleRings X.toRingedSpace).over U)
          (𝟙 ((moduleRings X.toRingedSpace).over U).obj) ⋙
          (Scheme.Modules.overEquiv U).functor ≅
        PresheafOfModules.pushforward₀OfCommRingCat
          (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj ⋙
          PresheafOfModules.sheafification.{u}
            (R₀ := (moduleRings U.toScheme.toRingedSpace).obj)
            (R := moduleRings U.toScheme.toRingedSpace)
            (𝟙 (moduleRings U.toScheme.toRingedSpace).obj)) := by sorry

end AlgebraicGeometry
