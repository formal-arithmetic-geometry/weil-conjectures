/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal

/-!

# The pullback `g^*` is symmetric monoidal, and `g^* ⊣ g_*` is a monoidal adjunction

For a morphism of schemes `g : Z ⟶ Y` and a closed symmetric monoidal coefficient category
`A`, the pushforward `g_*` on `A`-valued pro-étale sheaves is lax symmetric monoidal
(`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal`). This file
records the structure on the other half of the adjunction `g^* ⊣ g_*`, which is what the
module-object six functors need in order to transport ring objects and module objects along
`g^*`:

* `ProEtale.oplaxMonoidal_upperStar`: `g^*` is oplax monoidal, being the left adjoint of the
  lax monoidal `g_*` (`Adjunction.leftAdjointOplaxMonoidal`). This is formal.
* `ProEtale.isIso_η_upperStar` and `ProEtale.isIso_δ_upperStar`: the oplax structure maps
  `g^* 𝟙 ⟶ 𝟙` and `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` are isomorphisms, i.e. `g^*` is *strong*
  monoidal. This is the actual content of the file, and it is currently `sorry`ed, see below.
* `ProEtale.monoidal_upperStar`: the resulting strong monoidal structure on `g^*`, and
  `ProEtale.isMonoidal_upperStarLowerStarAdjunction`: the adjunction `g^* ⊣ g_*` is a monoidal
  adjunction in the sense of mathlib (`Adjunction.IsMonoidal`), the lax structure of `g_*` and
  the oplax structure of `g^*` being mates.
* `ProEtale.laxBraided_upperStar`: `g^*` is moreover (lax) braided, which is deduced from the
  lax braidedness of `g_*` by the mate correspondence. In particular `g^*` sends commutative
  ring objects to commutative ring objects (`Functor.isCommMonObj_obj`).

## Sorried input

* `ProEtale.isIso_η_upperStar` and `ProEtale.isIso_δ_upperStar`: the pullback `g^*` commutes
  with the tensor product of sheaves. The argument: the tensor product of sheaves is the
  sheafification of the objectwise tensor product of presheaves, `g^*` is the sheafification of
  the left Kan extension along the opposite of base change, and both sheafification and this
  Kan extension commute with the objectwise tensor product (the latter because the Kan extension
  is a colimit over the comma categories of base change, which are cofiltered since base change
  preserves finite limits, and filtered colimits commute with the tensor product, `A` being
  closed). For `g` weakly étale, `g^*` is restriction along the localization functor of the
  pro-étale sites, and the statement is the compatibility of sheafification with restriction
  along a continuous cocontinuous functor.
* `ProEtale.isMonoidal_lowerStarComp`: the composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of
  `ProEtale.lowerStarComp` is monoidal. Both lax monoidal structures are the sheafification of
  the objectwise one transported along the base change functors of the sites, and the
  composition isomorphism is induced by the pullback pasting isomorphism
  `(V ×_Z Y) ×_Y X ≅ V ×_Z X`, which is compatible with the objectwise tensor products. It is
  the input making the composition isomorphism of pushforwards of module objects
  (`ProEtale.CondensedRing.lowerStarComp`) available.

-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace AlgebraicGeometry

open Scheme ProEtale

/-! ### The strong monoidal structure on the pullback -/

section UpperStar

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

variable {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The pullback `g^*` on pro-étale sheaves is oplax monoidal, being left adjoint to the lax
monoidal pushforward `g_*`. -/
noncomputable instance ProEtale.oplaxMonoidal_upperStar : (g)^*[A].OplaxMonoidal :=
  (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal

/-- The oplax unit `g^* 𝟙 ⟶ 𝟙` of the pullback on pro-étale sheaves is an isomorphism: the
pullback of the unit sheaf is the unit sheaf. See the module docstring. -/
instance ProEtale.isIso_η_upperStar : IsIso (η (g)^*[A]) := sorry

/-- The oplax structure maps `g^* (F ⊗ G) ⟶ g^* F ⊗ g^* G` of the pullback on pro-étale sheaves
are isomorphisms: the pullback commutes with the tensor product of sheaves. See the module
docstring. -/
instance ProEtale.isIso_δ_upperStar (F G : Sheaf (Scheme.ProEt.topology Y) A) :
    IsIso (δ (g)^*[A] F G) := sorry

/-- The pullback `g^*` on pro-étale sheaves is strong monoidal: its oplax structure maps are
isomorphisms. -/
noncomputable instance ProEtale.monoidal_upperStar : (g)^*[A].Monoidal :=
  Functor.Monoidal.ofOplaxMonoidal _

/-- The adjunction `g^* ⊣ g_*` on pro-étale sheaves is a monoidal adjunction: the lax monoidal
structure of `g_*` and the (op)lax monoidal structure of `g^*` are mates. -/
instance ProEtale.isMonoidal_upperStarLowerStarAdjunction :
    (ProEtale.upperStarLowerStarAdjunction A g).IsMonoidal :=
  let h : letI := (ProEtale.upperStarLowerStarAdjunction A g).leftAdjointOplaxMonoidal
      (ProEtale.upperStarLowerStarAdjunction A g).IsMonoidal := inferInstance
  ⟨h.leftAdjoint_ε, h.leftAdjoint_μ⟩

/-- The pullback `g^*` on pro-étale sheaves is lax braided (hence braided, being strong
monoidal): the compatibility with the braiding is the mate of the one of `g_*`. When `A` is
symmetric, this says that `g^*` is symmetric monoidal. In particular `g^*` sends commutative
ring objects to commutative ring objects. -/
noncomputable instance ProEtale.laxBraided_upperStar : (g)^*[A].LaxBraided where
  braided F G := by
    have h : δ (g)^*[A] F G ≫ (β_ ((g)^*[A].obj F) ((g)^*[A].obj G)).hom =
        (g)^*[A].map (β_ F G).hom ≫ δ (g)^*[A] G F := by
      change ((ProEtale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm
          (((ProEtale.upperStarLowerStarAdjunction A g).unit.app F ⊗ₘ
            (ProEtale.upperStarLowerStarAdjunction A g).unit.app G) ≫ μ (g)_*[A] _ _) ≫ _ =
        _ ≫ ((ProEtale.upperStarLowerStarAdjunction A g).homEquiv _ _).symm
          (((ProEtale.upperStarLowerStarAdjunction A g).unit.app G ⊗ₘ
            (ProEtale.upperStarLowerStarAdjunction A g).unit.app F) ≫ μ (g)_*[A] _ _)
      rw [← Adjunction.homEquiv_naturality_right_symm]
      erw [← Adjunction.homEquiv_naturality_left_symm]
      rw [Category.assoc, Functor.LaxBraided.braided]
      erw [BraidedCategory.braiding_naturality_assoc]
      rfl
    rw [← cancel_epi (δ (g)^*[A] F G), Functor.Monoidal.δ_μ_assoc, reassoc_of% h,
      Functor.Monoidal.δ_μ, Category.comp_id]

end UpperStar

/-! ### The composition isomorphism of pushforwards is monoidal -/

section LowerStarComp

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalClosed A]

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The composition isomorphism `f_* ⋙ g_* ≅ (f ≫ g)_*` of pushforwards on pro-étale sheaves is
a monoidal natural isomorphism, for the composite lax monoidal structure on `f_* ⋙ g_*`. See
the module docstring. -/
instance ProEtale.isMonoidal_lowerStarComp :
    NatTrans.IsMonoidal (ProEtale.lowerStarComp A f g).hom := sorry

end LowerStarComp

end AlgebraicGeometry
