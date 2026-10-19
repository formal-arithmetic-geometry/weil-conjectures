/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NN
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Abelian.RightDerived

import WeilConjectures.SixFunctors.Integral.Exact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.Abelian.ExactFunctorHigherDerivedVanishing

/-!
# Exactness of integral étale direct image

Source: Stacks Project, Étale Cohomology, Tag 04C2, parts (1) and (4), and Derived
Categories, Tag 015F (blueprint: sbc-lem-integral-etale-direct-image-exact).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Transport integral module direct-image exactness across the integer-module equivalence.
The two coefficient functors are left adjoints on sheaves, and their composite around
module direct image is naturally isomorphic to abelian direct image. -/
private theorem preservesFiniteColimits_integral_ab {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegralHom f] :
    PreservesFiniteColimits (lowerStar AddCommGrpCat.{u + 1} f) := by
  let U := forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) AddCommGrpCat.{u + 1}
  have : U.IsEquivalence := by
    change (ModuleCat.restrictScalars
      (ULift.ringEquiv.symm : ℤ ≃+* ULift.{u + 1} ℤ).toRingHom ⋙
        forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).IsEquivalence
    infer_instance
  let e := U.asEquivalence
  let L := sheafCompose X.smallEtaleTopology e.inverse
  let R := sheafCompose Y.smallEtaleTopology U
  have : L.IsLeftAdjoint :=
    (sheafComposeAdjunction X.smallEtaleTopology e.symm.toAdjunction).isLeftAdjoint
  have : R.IsLeftAdjoint :=
    (sheafComposeAdjunction Y.smallEtaleTopology e.toAdjunction).isLeftAdjoint
  have := preservesFiniteColimits_lowerStar_of_isIntegralHom (ULift.{u + 1} ℤ) f
  let T := L ⋙ lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f ⋙ R
  have : PreservesFiniteColimits T := by
    apply comp_preservesFiniteColimits
  let i : T ≅ lowerStar AddCommGrpCat.{u + 1} f := NatIso.ofComponents
    (fun F ↦ (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (Functor.isoWhiskerLeft ((lowerStar AddCommGrpCat.{u + 1} f).obj F).obj e.counitIso ≪≫
        Functor.rightUnitor _))
    (by
      intro F G φ
      apply (fullyFaithfulSheafToPresheaf _ _).map_injective
      apply NatTrans.ext
      funext W
      exact e.counitIso.hom.naturality
        (φ.hom.app (Opposite.op
          ((MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f).obj W.unop))))
  exact preservesFiniteColimits_of_natIso i

/-- Integral direct image on abelian étale sheaves is exact, its positive right derived
functors vanish, and its canonical bounded-below derived comparison is invertible.
Source: Stacks Project, Tags 04C2 and 015F
(blueprint: sbc-lem-integral-etale-direct-image-exact).

Proof: Given an epimorphism of sheaves and a section of its direct image over an étale
object `V`, the local-surjectivity criterion gives a covering of `X ×_Y V` on which the
section lifts. At every point of `V`, the integral disjoint-refinement lemma supplies an
étale neighbourhood on which that covering refines to a disjoint open partition. Pull the
local lifts back to the pieces and glue using the disjoint-cover product formula, also
for the empty partition. Uniqueness of gluing shows that the glued section maps to the
original section. These neighbourhoods jointly cover `V`, so the local-surjectivity
criterion proves that direct image preserves epimorphisms. Direct image is already
additive and left exact; thus it is exact. Enough injectives and the exact-functor
higher-derived-vanishing lemma imply that every positive right derived functor is zero.
Finally, exact-functor derived factorization and preservation of bounded-below objects
identify the termwise functor with the right derived functor by its universal property:
the canonical comparison is invertible on every bounded-below complex. Passing to its
homotopy class gives the displayed comparison on `HomotopyCategory.Plus`. For finite
morphisms this specializes to `lemma-weil-pbc-finite-direct-image-exact`. -/
theorem integral_etale_direct_image_exact {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] :
    (PreservesFiniteLimits (lowerStar AddCommGrpCat.{u + 1} f) ∧
      PreservesFiniteColimits (lowerStar AddCommGrpCat.{u + 1} f)) ∧
    (∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ),
      IsZero (((lowerStar AddCommGrpCat.{u + 1} f).rightDerived (q + 1)).obj F)) ∧
    (∀ K : HomotopyCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsIso ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusUnit.app K)) := by
  have := preservesFiniteColimits_integral_ab f
  refine ⟨⟨inferInstance, inferInstance⟩, ?_, ?_⟩
  · intro F q
    exact Functor.isZero_rightDerived_obj_of_exact _ F q
  · intro K
    have := Functor.isIso_rightDerivedFunctorPlusUnit (lowerStar AddCommGrpCat.{u + 1} f)
    exact NatIso.hom_app_isIso
      (asIso (lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlusUnit) K

end AlgebraicGeometry.Etale
