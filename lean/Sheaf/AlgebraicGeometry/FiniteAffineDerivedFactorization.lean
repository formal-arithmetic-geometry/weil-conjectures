/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Sheaf.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Derived pushforward through the direct-image algebra

Source: Stacks Project, Tag 0AVW, final pushforward identification
(blueprint: lem-sc-finite-affine-derived-factorization).
-/

@[expose] public section

universe u wX wY wA

open CategoryTheory

namespace AlgebraicGeometry

set_option maxHeartbeats 400000 in
-- Unfolding the two ring-sheaf presentations and the derived composition consumes extra heartbeats.
/-- Scalar restriction of the algebra-valued derived pushforward is the scheme pushforward.
Source: Stacks Project, Tag 0AVW, final pushforward identification
(blueprint: lem-sc-finite-affine-derived-factorization).

Proof: Restriction of scalars is exact, since the underlying abelian sheaf, kernels,
images, and cokernels are unchanged. Its right derived functor therefore agrees with
termwise restriction after localization, with the canonical comparison. Choose the
functorial K-injective representative I on X used for derived direct image. The
complexes g_* I and f_* I have identical underlying sheaves and different scalar
structures; restriction of the former is naturally the latter. The localization
comparisons identify both composites with this complex-level functor. Full faithfulness
of precomposition by localization descends this natural identity to the asserted
isomorphism on the entire derived category. No boundedness or quasi-coherence of the
input is needed; the zero complex and every shift use the same calculation. -/
theorem finite_affine_derived_factorization {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsFinite f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f)))]
    : Nonempty (RingedSpace.derivedModuleDirectImage (toDirectImageAlgebraSpace f) ⋙
        (SheafOfModules.restrictScalars
          (R := moduleRings Y.toRingedSpace)
          (R' := moduleRings (directImageAlgebraSpace f))
          ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ≅
          schemeDerivedDirectImage f) := by
  let F := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let S := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace f))
    ⟨Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)⟩
  let instB : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat)).obj
        ((Under.mk (⟨f.c⟩ : Y.sheaf ⟶
          (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf)).right))) :=
    inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace f))))
  have : CategoryTheory.Limits.PreservesFiniteLimits S :=
    sheafAlgebraRestrictScalars_preservesFiniteLimits Y
      (Under.mk (⟨f.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf))
  have : CategoryTheory.Limits.PreservesFiniteColimits S :=
    sheafAlgebraRestrictScalars_preservesFiniteColimits Y
      (Under.mk (⟨f.c⟩ : Y.sheaf ⟶
        (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf))
  let e : F ⋙ S ≅ RingedSpace.moduleDirectImage f.toLRSHom.toShHom := Iso.refl _
  exact ⟨Functor.isoWhiskerLeft F.rightDerivedFunctor
      S.rightDerivedFunctorIsoMapDerivedCategory ≪≫
    (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).symm ≪≫
    Functor.rightDerivedFunctorNatIso e⟩

end AlgebraicGeometry
