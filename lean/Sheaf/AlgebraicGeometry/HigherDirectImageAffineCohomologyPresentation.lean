/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.OpenModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.Topology.RestrictInjectiveResolution

/-! # Affine-local presentation of ordinary higher direct images

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-affine-cohomology-presentation).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Cohomology on inverse-image opens maps naturally to sections of ordinary higher
 direct image, and these classes detect maps out of that higher direct image on the
 affine basis. No compactness, separation or coproduct hypothesis is needed.

Source: Stacks Project, Cohomology, Tags 01E1 and 01E4.
(blueprint: lem-pc-higher-direct-image-affine-cohomology-presentation).

Proof: For an open V of Y, restrict an injective module resolution on X to
U = f^{-1}(V). Open restriction is exact and preserves injectives (01E1). Taking
sections on U therefore computes the cohomology of the restricted module. The
resolution comparison identifies this group with the value at V of the presheaf
H^p(f_*I). Compose with the canonical cocycle-to-cohomology-sheaf map theta and
with the inverse of the resolution isomorphism H^p(f_*I) = R^p f_*M. A lift of a
coefficient morphism to injective resolutions commutes with restriction, sections,
theta and the resolution isomorphisms; homotopic lifts induce equal maps. Thus these
maps form the displayed natural transformations, independent of resolutions.
For the detection assertion, the canonical cohomology-presheaf map induces an
isomorphism on stalks (01E4). Every germ of R^p f_*N is consequently represented
locally by such a cohomology class. Shrink its representing open to an affine
neighborhood; restriction of resolutions identifies the restricted class with the
corresponding class on its inverse image. If the composites with a and b agree on
all these classes, their maps on every stalk agree. Sheaf morphisms are determined
by their maps on stalks, hence a = b. For an empty Y this is vacuous because there
is only one module-sheaf morphism. For p = 0 it is the ordinary sections comparison.
This statement concerns arbitrary maps out of one higher direct image; it asserts
no preservation of coproducts. -/
theorem higherDirectImage_affine_cohomology_presentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) (p : ℕ) :
    ∃ c : ∀ V : Y.Opens,
      Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι ⋙
        RingedSpace.moduleCohomology (f ⁻¹ᵁ V).toScheme.toRingedSpace p ⋙
          forget₂ (ModuleCat.{u}
            ((moduleRings (f ⁻¹ᵁ V).toScheme.toRingedSpace).obj.obj (Opposite.op ⊤)))
              AddCommGrpCat.{u} ⟶
      (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p ⋙
        RingedSpace.openModuleSections Y.toRingedSpace V,
      ∀ (N : X.Modules) (Q : Y.Modules)
        (a b : ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).obj N ⟶ Q),
        (∀ (V : Y.Opens), IsAffineOpen V →
          (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map a =
            (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map b) →
        a = b := by sorry

end AlgebraicGeometry
