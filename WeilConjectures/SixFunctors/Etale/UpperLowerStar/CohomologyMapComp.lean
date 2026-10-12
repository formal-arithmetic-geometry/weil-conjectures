/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-!
# Composition of pullback maps on étale cohomology

For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ Z`, pulling a cohomology class back along
`g` and then along `f` is pulling it back along `f ≫ g`, up to the canonical isomorphisms
`(f ≫ g)^* F ≅ f^* g^* F` of coefficient sheaves and an automorphism of the constant sheaf `ℤ`
on `X`. In particular the composite of the two pullback maps is bijective if and only if the
pullback map along `f ≫ g` is.

## Main statements

- `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap`: the composition formula.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_comp_iff`: bijectivity of the composite.
-/

@[expose] public section

universe u

open CategoryTheory Limits Abelian

namespace AlgebraicGeometry.Etale

variable {X Y Z : Scheme.{u}}

/-- The automorphism of the constant sheaf `ℤ` on `X` relating the pullback maps along `g`,
then `f`, and along `k = f ≫ g`, see `AlgebraicGeometry.Etale.cohomologyMap_cohomologyMap`. -/
noncomputable def cohomologyMapCompIso (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k) :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app _ ≪≫
    ((f)^*[AddCommGrpCat.{u + 1}]).mapIso
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).symm.app _) ≪≫
    (upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).symm.app _ ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} k).app _

/-- **Composition of pullback maps on étale cohomology.** Pulling a class back along
`g : Y ⟶ Z` and then along `f : X ⟶ Y` is pulling it back along `k = f ≫ g`, up to the
composition isomorphism `k^* F ≅ f^* g^* F` and an automorphism of the constant sheaf `ℤ`.
(blueprint: `lem-weil-pbc-cohomology-pullback-functorial`, composition) -/
theorem cohomologyMap_cohomologyMap (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) {n : ℕ} (x : Sheaf.H F n) :
    cohomologyMap f _ n (cohomologyMap g F n x) =
      (Ext.mk₀ (cohomologyMapCompIso f g k hk).hom).comp
        ((cohomologyMap k F n x).comp
          (Ext.mk₀ ((upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).hom.app F)) (add_zero n))
        (zero_add n) := by
  have : EnoughInjectives (Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) := inferInstance
  rw [cohomologyMap_apply, cohomologyMap_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mapExactFunctor _ _ _
      (upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm)]
  simp only [cohomologyMapCompIso, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc,
    Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_app]
  exact congrArg (fun t ↦ (Ext.mk₀ t).comp _ (zero_add n)) (by simp)

/-- Pre- and postcomposition with the classes of isomorphisms is a bijection of `Ext`-groups. -/
lemma bijective_mk₀_comp_comp_mk₀ {C : Type*} [Category C] [Abelian C] [HasExt C]
    {A A' B B' : C} (e : A' ⟶ A) [IsIso e] (e' : B ⟶ B') [IsIso e'] (n : ℕ) :
    Function.Bijective (fun z : Ext A B n ↦
      (Ext.mk₀ e).comp (z.comp (Ext.mk₀ e') (add_zero n)) (zero_add n)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun z ↦ (Ext.mk₀ (inv e)).comp (z.comp (Ext.mk₀ (inv e')) (add_zero n)) (zero_add n),
      fun z ↦ ?_, fun z ↦ ?_⟩ <;>
  simp [Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀]

/-- The composite of the pullback maps along `g : Y ⟶ Z` and `f : X ⟶ Y` is bijective if and
only if the pullback map along `f ≫ g` is. -/
theorem bijective_cohomologyMap_comp_iff (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z) (hk : f ≫ g = k)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : ℕ) :
    Function.Bijective (cohomologyMap f _ n ∘ cohomologyMap g F n) ↔
      Function.Bijective (cohomologyMap k F n) := by
  have : (cohomologyMap f _ n ∘ cohomologyMap g F n) =
      (fun z ↦ (Ext.mk₀ (cohomologyMapCompIso f g k hk).hom).comp
        (z.comp (Ext.mk₀ ((upperStarComp AddCommGrpCat.{u + 1} f g k hk.symm).hom.app F))
          (add_zero n)) (zero_add n)) ∘ cohomologyMap k F n :=
    funext fun x ↦ cohomologyMap_cohomologyMap f g k hk F x
  rw [this]
  exact (Function.Bijective.of_comp_iff' (bijective_mk₀_comp_comp_mk₀ _ _ n) _)

end AlgebraicGeometry.Etale
