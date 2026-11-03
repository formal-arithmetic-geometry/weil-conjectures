/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
/-! # Filtered colimits of the specified ringed-topos module pullback

Source: Stacks Project, Modules on Sites, Tag 03D7,
lemma-adjoint-pullback-pushforward-modules.
(blueprint: lem-weil-pbc-ringed-topos-pullback-filtered-colimits).

The scalar-extension Hom equivalence generalizes the private construction in
ModulePullbackPushforwardAdjunction to independent site and coefficient universes.
The inverse-image argument uses only the supplied natural underlying-sheaf isomorphism. -/

@[expose] public section
universe u v w uD vD uC vC
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
  {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

open scoped ChangeOfRings
set_option backward.isDefEq.respectTransparency false

private abbrev ringSheaf {C : Type u} [Category.{v} C] [EssentiallySmall.{w} C]
    {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{w}) :=
  (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj R
private noncomputable abbrev restriction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :=
  restrictScalars.{w} ((sheafCompose K (forget₂ CommRingCat.{w} RingCat.{w})).map c)

private theorem tensorRestriction_tmul
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) (M : SheafOfModules.{w} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{vD, uD, w} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{vD, uD, w} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :
    SheafOfModules.{w} (ringSheaf A) ⥤ PresheafOfModules.{w} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{vD, uD, w} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{vD, uD, w} c M ⟶
      changeOfRingsPresheaf.{vD, uD, w} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{vD, uD, w} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) :
    SheafOfModules.{w} (ringSheaf A) ⥤ SheafOfModules.{w} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S))
    (f : changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{vD, uD, w} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul, map_one]
    have atOne (W : Dᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S)) :
    (changeOfRingsPresheaf.{vD, uD, w} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
  toFun := tensorToRestriction c M H
  invFun := restrictionToTensor c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv (c.hom.app W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A)) (H : SheafOfModules.{w} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    {M N : SheafOfModules.{w} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{w} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{vD, uD, w} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S)
    (M : SheafOfModules.{w} (ringSheaf A))
    {H H' : SheafOfModules.{w} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D] {K : GrothendieckTopology D}
    {A S : Sheaf K CommRingCat.{w}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

end SheafOfModules
