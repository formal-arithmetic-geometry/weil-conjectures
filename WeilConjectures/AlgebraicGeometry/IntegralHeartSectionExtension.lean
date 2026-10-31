/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Restrict

/-! # Sectionwise scalar extension before sheafification

The tensor adjunction is compatible with the restriction maps, with independent
site and coefficient universes. Source: Stacks Project, Tag 03EK
(blueprint: lem-integral-heart-section-extension).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe c h r
open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace PresheafOfModules.IntegralHeart

variable {C : Type c} [Category.{h} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose
    (forget₂ CommRingCat.{r} RingCat.{r})]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{r}]
  {R S : Cᵒᵖ ⥤ CommRingCat.{r}} (α : R ⟶ S)

def bottomRing (R : Cᵒᵖ ⥤ CommRingCat.{r}) :
    Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{r} :=
  ⟨R, Presheaf.isSheaf_bot _⟩

def bottomModule (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat)) :
    SheafOfModules.{r}
      ((sheafCompose (⊥ : GrothendieckTopology C)
        (forget₂ CommRingCat.{r} RingCat.{r})).obj (bottomRing.{c, h, r} R)) :=
  ⟨M, Presheaf.isSheaf_bot _⟩

def bottomMap : bottomRing.{c, h, r} R ⟶ bottomRing.{c, h, r} S := ⟨α⟩

/-- Extend coefficients sectionwise, with the tensor restriction maps. -/
def sectionExtension : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat) ⥤
    PresheafOfModules.{r} (S ⋙ forget₂ CommRingCat RingCat) where
  obj M := SheafOfModules.changeOfRingsPresheafOfUniverses.{h, c, r, r}
    (bottomMap.{c, h, r} (C := C) (R := R) (S := S) α)
    (bottomModule.{c, h, r} (C := C) (R := R) M)
  map {M N} f :=
    { app U := (ModuleCat.extendScalars (α.app U).hom).map (f.app U)
      naturality := SheafOfModules.changeOfRingsHom_naturalityOfUniverses.{h, c, r, r}
        (bottomMap.{c, h, r} (C := C) (R := R) (S := S) α)
        (bottomModule.{c, h, r} (C := C) (R := R) M)
        (N := bottomModule.{c, h, r} (C := C) (R := R) N) ⟨f⟩ }
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_id _
  map_comp f g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.extendScalars (α.app U).hom).map_comp _ _

/-- Restriction acts on the two tensor factors separately. -/
theorem sectionExtension_map_tmul
    (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    {U V : Cᵒᵖ} (i : U ⟶ V) (s : S.obj U) (m : M.obj U) :
    ((sectionExtension α).obj M).map i (s ⊗ₜ[R.obj U, (α.app U).hom] m) =
      S.map i s ⊗ₜ[R.obj V, (α.app V).hom] M.map i m :=
  SheafOfModules.changeOfRingsMap_tmulOfUniverses.{h, c, r, r}
    (bottomMap.{c, h, r} (C := C) (R := R) (S := S) α)
    (bottomModule.{c, h, r} (C := C) (R := R) M) i s m

omit [(⊥ : GrothendieckTopology C).HasSheafCompose
    (forget₂ CommRingCat.{r} RingCat.{r})]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{r}] in
theorem lift_one (U : Cᵒᵖ) (M : ModuleCat.{r} (R.obj U))
    (N : ModuleCat.{r} (S.obj U))
    (g : M ⟶ (ModuleCat.restrictScalars (α.app U).hom).obj N) (m : M) :
    ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm g
      ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] m) = g m :=
  congrArg (fun f ↦ f m)
    (((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).apply_symm_apply g)

def sectionHomEquiv
    (M : PresheafOfModules.{r} (R ⋙ forget₂ CommRingCat RingCat))
    (N : PresheafOfModules.{r} (S ⋙ forget₂ CommRingCat RingCat)) :
    ((sectionExtension α).obj M ⟶ N) ≃
      (M ⟶ (restrictScalars (Functor.whiskerRight α (forget₂ CommRingCat RingCat))).obj N)
    where
  toFun f :=
    { app U := (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _ (f.app U)
      naturality := by
        intro U V i
        apply ModuleCat.hom_ext
        ext m
        have h := naturality_apply f i
          ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] m)
        change f.app V ((1 : S.obj V) ⊗ₜ[R.obj V, (α.app V).hom] M.map i m) =
          N.map i (f.app U ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] m))
        simpa only [sectionExtension_map_tmul, map_one] using h }
  invFun g :=
    { app U := ((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm
        (g.app U)
      naturality := by
        intro U V i
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        have h := naturality_apply g i m
        change (((ModuleCat.extendRestrictScalarsAdj (α.app V).hom).homEquiv _ _).symm
          (g.app V)) ((((sectionExtension α).obj M).map i)
            ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] m)) =
          N.map i ((((ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv _ _).symm
            (g.app U)) ((1 : S.obj U) ⊗ₜ[R.obj U, (α.app U).hom] m))
        rw [sectionExtension_map_tmul, map_one]
        erw [lift_one, lift_one]
        exact h }
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    exact Equiv.symm_apply_apply _ _
  right_inv g := by
    apply PresheafOfModules.hom_ext
    intro U
    exact Equiv.apply_symm_apply _ _

/-- The ordinary tensor adjunction, compatible with all restriction maps.

Source: Stacks Project, Tag 03EK (blueprint: lem-integral-heart-section-extension).
Proof: transpose each component by the tensor adjunction. The transpose evaluates at
1 tensor m, so naturality follows by restricting that tensor. Conversely, extend a
restricted-linear map by s tensor m to s times its value on m. The tensor generators
prove restriction compatibility and the inverse identities. Naturality in both modules
is the sectionwise tensor adjunction naturality. -/
def sectionAdjunction : sectionExtension α ⊣
    restrictScalars (Functor.whiskerRight α (forget₂ CommRingCat RingCat)) :=
  Adjunction.mkOfHomEquiv
    { homEquiv := sectionHomEquiv α
      homEquiv_naturality_left_symm := by
        intro M M' N f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv_naturality_left_symm
          (f.app U) (g.app U)
      homEquiv_naturality_right := by
        intro M N N' f g
        apply PresheafOfModules.hom_ext
        intro U
        exact (ModuleCat.extendRestrictScalarsAdj (α.app U).hom).homEquiv_naturality_right
          (f.app U) (g.app U) }

end PresheafOfModules.IntegralHeart

namespace PresheafOfModules.IntegralHeart

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose
    (forget₂ CommRingCat.{r} RingCat.{r})]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)

def rawComparison
    (M : SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    SheafOfModules.changeOfRingsPresheafOfUniverses α M ≅
      (sectionExtension α.hom).obj M.val := by
  refine PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_
  intro U V i
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (SheafOfModules.changeOfRingsPresheafOfUniverses α M).map i
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m) =
      ((sectionExtension α.hom).obj M.val).map i
        ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (α.hom.app U).hom] m)
  rw [sectionExtension_map_tmul]
  exact SheafOfModules.changeOfRingsMap_tmulOfUniverses α M i 1 m

end PresheafOfModules.IntegralHeart

namespace PresheafOfModules.IntegralHeart

variable {C : Type c} [Category.{h} C] {J : GrothendieckTopology C}
  [(⊥ : GrothendieckTopology C).HasSheafCompose
    (forget₂ CommRingCat.{r} RingCat.{r})]
  [(⊥ : GrothendieckTopology C).WEqualsLocallyBijective AddCommGrpCat.{r}]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasWeakSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)

/-- Scalar extension obtained by tensoring sections and sheafifying. -/
def sheafSectionExtension :
    SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{r} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj S) :=
  SheafOfModules.forget _ ⋙ sectionExtension α.hom ⋙
    sheafification (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
      (𝟙 _)

/-- The tensor adjunction restricts to the full subcategories of sheaves. -/
def sheafSectionAdjunction : sheafSectionExtension α ⊣
    SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat RingCat)).map α) :=
  ((sectionAdjunction α.hom).comp (sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _))).restrictFullyFaithful
    (SheafOfModules.fullyFaithfulForget _)
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

/-- Tensor extension commutes with module sheafification along a locally bijective
coefficient map. Both sides represent the same restriction-of-scalars functor.

Source: Stacks Project, Tag 03EK
(blueprint: lem-integral-heart-section-extension).
Proof: transpose maps sectionwise by the tensor adjunction. The value on 1 tensor m
makes the restriction and functoriality squares commute. Compose this adjunction
with module sheafification, and restrict along the fully faithful inclusions of
sheaves. For the two displayed composites the right adjoints agree: forget the
sheaf and restrict scalars along the composite coefficient map. Uniqueness of
left adjoints gives the natural isomorphism. -/
def sheafificationSectionExtensionIso
    {P : Cᵒᵖ ⥤ CommRingCat.{r}} (η : P ⟶ R.obj)
    [Presheaf.IsLocallyInjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat))]
    [Presheaf.IsLocallySurjective J (Functor.whiskerRight η (forget₂ CommRingCat RingCat))] :
    sheafification (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
      (Functor.whiskerRight η (forget₂ CommRingCat RingCat)) ⋙
        sheafSectionExtension α ≅
      sectionExtension (η ≫ α.hom) ⋙
        sheafification (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S)
          (𝟙 _) :=
  ((sheafificationAdjunction
    (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj R)
    (Functor.whiskerRight η (forget₂ CommRingCat RingCat))).comp
      (sheafSectionAdjunction α)).leftAdjointUniq
    (((sectionAdjunction (η ≫ α.hom)).comp (sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat RingCat)).obj S) (𝟙 _))).ofNatIsoRight
        (Iso.refl _))

end PresheafOfModules.IntegralHeart
