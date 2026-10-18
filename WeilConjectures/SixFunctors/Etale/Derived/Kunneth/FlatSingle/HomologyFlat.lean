/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.FlatSingle.Homology
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-!
# The degree-wise base change map at a flat sheaf

Fix a commutative square `h ≫ f' = e ≫ g`, `p : X' ⟶ X` and a sheaf `𝓕` on `T`. For a flat sheaf
`𝓖` on `X`, the degree-`q` base change map
(`AlgebraicGeometry.Etale.tensorBaseChangeHomologyMap`) at `𝓖` is, up to isomorphisms, the map
induced on `Hᵠ` by the base change map
`Lp^* 𝓖[0] ⊗ᴸ Lf'^* Rg_* 𝓕[0] ⟶ Rh_* (Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0])`
(`AlgebraicGeometry.Etale.tensorBaseChangeMap`). Hence the latter is an isomorphism if and only
if all the degree-wise maps are
(`AlgebraicGeometry.Etale.isIso_tensorBaseChangeMap_iff_forall_isIso_tensorBaseChangeHomologyMap`).
This is used in the proof of blueprint `lem-kun-0f1j`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- For `A` of Tor amplitude in `[0, 0]` (for instance a flat sheaf placed in degree `0`), the
truncation `τ^{≤q} N ⟶ N` induces an isomorphism `Hᵠ(A ⊗ᴸ τ^{≤q} N) ≅ Hᵠ(A ⊗ᴸ N)`. -/
lemma isIso_homologyFunctor_map_whiskerLeft_truncLEι {C : Type*} [Category C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C] [MonoidalCategory C]
    [MonoidalClosed C] [MonoidalPreadditive C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    [DerivedCategory.Qh.HasDerivedMonoidalCategory
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    {A : DerivedCategory C} (hA : DerivedCategory.torAmplitudeIn C 0 0 A)
    (N : DerivedCategory C) (q : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C q).map
      (A ◁ (DerivedCategory.TStructure.t.truncLEι q).app N)) := by
  let T := (DerivedCategory.TStructure.t.triangleLEGE q (q + 1) rfl).obj N
  have hT : T ∈ distTriang _ := DerivedCategory.TStructure.t.triangleLEGE_distinguished q (q + 1)
    rfl N
  have hT' := ((curriedTensor (DerivedCategory C)).obj A).map_distinguished T hT
  have : T.obj₃.IsGE (q + 1) :=
    inferInstanceAs ((DerivedCategory.TStructure.t.truncGE (q + 1)).obj N).IsGE (q + 1)
  have h₃ := DerivedCategory.isGE_tensor_of_torAmplitudeIn hA T.obj₃ (q + 1)
  have hmono : Mono ((DerivedCategory.homologyFunctor C q).map
      (((curriedTensor (DerivedCategory C)).obj A).mapTriangle.obj T).mor₁) := by
    rw [DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT' (q - 1) q (by lia)]
    exact ((A ⊗ T.obj₃).isZero_of_isGE (0 + (q + 1)) (q - 1) (by lia)).eq_of_src _ _
  have hepi : Epi ((DerivedCategory.homologyFunctor C q).map
      (((curriedTensor (DerivedCategory C)).obj A).mapTriangle.obj T).mor₁) := by
    rw [DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT' q]
    exact ((A ⊗ T.obj₃).isZero_of_isGE (0 + (q + 1)) q (by lia)).eq_of_tgt _ _
  exact isIso_of_mono_of_epi ((DerivedCategory.homologyFunctor C q).map
      (((curriedTensor (DerivedCategory C)).obj A).mapTriangle.obj T).mor₁)

variable (Λ : Type (u + 1)) [CommRing Λ] {X X' S' T Y : Scheme.{u}} (p : X' ⟶ X) (h : Y ⟶ X')
  (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S') (w : h ≫ f' = e ≫ g)
  (𝓕 : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))

/-- At a flat sheaf `𝓖`, the degree-`q` base change map is an isomorphism if and only if the base
change map `Lp^* 𝓖[0] ⊗ᴸ Lf'^* Rg_* 𝓕[0] ⟶ Rh_* (Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0])` induces an
isomorphism on `Hᵠ`. -/
lemma isIso_tensorBaseChangeHomologyMap_app_iff
    (𝓖 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h𝓖 : ObjectProperty.flat 𝓖) (q : ℤ) :
    IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app 𝓖) ↔
      IsIso ((DerivedCategory.homologyFunctor _ q).map
        (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
          (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓖))
          ((DerivedCategory.singleFunctor _ 0).obj 𝓕))) := by
  have hA : DerivedCategory.torAmplitudeIn _ 0 0
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓖)) :=
    (DerivedCategory.torAmplitudeIn _ 0 0).prop_of_iso
      ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) p).app 𝓖).symm
      (DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (UpperStarPreservesFlat.preservesFlat _ h𝓖))
  have h₁ : IsIso ((tensorBaseChangeHomologyTrunc Λ p f' g 𝓕 q).app 𝓖) :=
    isIso_homologyFunctor_map_whiskerLeft_truncLEι hA _ q
  have h₂ : IsIso ((tensorBaseChangeHomologyComparison Λ p h e 𝓕 q).app 𝓖) := by
    have := (isIso_singleFunctorTensorToSingle_app ((e)^*[ModuleCat.{u + 1} Λ].obj 𝓕) _
        (UpperStarPreservesFlat.preservesFlat _ (UpperStarPreservesFlat.preservesFlat _ h𝓖)))
    simp only [tensorBaseChangeHomologyComparison, Functor.whiskerLeft_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Category.comp_id]
    infer_instance
  rw [tensorBaseChangeHomologyMap, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    isIso_comp_left_iff, isIso_comp_right_iff, isIso_comp_right_iff]
  rfl

/-- At a flat sheaf `𝓖`, the base change map
`Lp^* 𝓖[0] ⊗ᴸ Lf'^* Rg_* 𝓕[0] ⟶ Rh_* (Lh^* Lp^* 𝓖[0] ⊗ᴸ Le^* 𝓕[0])` is an isomorphism if and
only if all the degree-wise base change maps are. -/
lemma isIso_tensorBaseChangeMap_iff_forall_isIso_tensorBaseChangeHomologyMap
    (𝓖 : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (h𝓖 : ObjectProperty.flat 𝓖) :
    IsIso (tensorBaseChangeMap (ModuleCat.{u + 1} Λ) h e f' g w
        (L((p)^*[ModuleCat.{u + 1} Λ]).obj ((DerivedCategory.singleFunctor _ 0).obj 𝓖))
        ((DerivedCategory.singleFunctor _ 0).obj 𝓕)) ↔
      ∀ q, IsIso ((tensorBaseChangeHomologyMap Λ p h e f' g w 𝓕 q).app 𝓖) := by
  rw [DerivedCategory.isIso_iff]
  exact forall_congr' fun q ↦ (isIso_tensorBaseChangeHomologyMap_app_iff Λ p h e f' g w 𝓕 𝓖 h𝓖
    q).symm

end Etale

end AlgebraicGeometry
