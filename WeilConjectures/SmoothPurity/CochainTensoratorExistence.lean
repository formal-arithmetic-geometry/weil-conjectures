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
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.SmoothPurity.CochainInverseComparison

/-! # Ordinary tensorator for independent site sizes

Source: Stacks Project, Modules on Sites, Tag 03EL.
(blueprint: lem-pur-independent-ringed-tensorator-existence).

The insertion is constructed on sections by the sheafification of `1 ⊗ m`.
Scalar extension and the normalized composite tensorator are constructed below.
The proof uses only tensor preservation of the specified algebraic inverse image.
-/

@[expose] public section

universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ChangeOfRings TensorProduct
namespace SheafOfModules.CochainScalarConstruction
set_option autoImplicit false
set_option maxErrors 5
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
private abbrev ringSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

private noncomputable abbrev restriction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :=
  restrictScalars ((sheafCompose K (forget₂ CommRingCat RingCat)).map c)

private theorem tensorRestriction_tmul
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A))
    {X Y : Dᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (changeOfRingsPresheaf.{vC, uC, u} c M).map i (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (exists_changeOfRingsMap.{vC, uC, u} c M i) s m

private noncomputable def tensorPresheafFunctor
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ PresheafOfModules.{u} (ringSheaf S).obj where
  obj M := changeOfRingsPresheaf.{vC, uC, u} c M
  map {M N} f :=
    show changeOfRingsPresheaf.{vC, uC, u} c M ⟶
      changeOfRingsPresheaf.{vC, uC, u} c N from
    { app := fun W ↦ (ModuleCat.extendScalars (c.hom.app W).hom).map (f.val.app W)
      naturality := changeOfRingsHom_naturality.{vC, uC, u} c _ f }
  map_id M := by
    ext W : 1
    change (ModuleCat.extendScalars (c.hom.app W).hom).map (𝟙 _) = _
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_id _
  map_comp f g := by
    ext W : 1
    exact (ModuleCat.extendScalars (c.hom.app W).hom).map_comp _ _

private noncomputable def tensorFunctor
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) :
    SheafOfModules.{u} (ringSheaf A) ⥤ SheafOfModules.{u} (ringSheaf S) :=
  tensorPresheafFunctor c ⋙ PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)

private noncomputable def tensorToRestriction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (f : changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val) : M ⟶ (restriction c).obj H where
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
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S))
    (g : M ⟶ (restriction c).obj H) : changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (c.hom.app Y).hom (g.val.app Y)
        ((changeOfRingsPresheaf.{vC, uC, u} c M).map i
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
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    (changeOfRingsPresheaf.{vC, uC, u} c M ⟶ H.val) ≃ (M ⟶ (restriction c).obj H) where
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
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A)) (H : SheafOfModules.{u} (ringSheaf S)) :
    ((tensorFunctor c).obj M ⟶ H) ≃ (M ⟶ (restriction c).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv c M H)

private theorem tensorHomEquiv_naturality_left
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    {M N : SheafOfModules.{u} (ringSheaf A)} (a : M ⟶ N)
    (H : SheafOfModules.{u} (ringSheaf S)) (f : (tensorFunctor c).obj N ⟶ H) :
    tensorHomEquiv c M H ((tensorFunctor c).map a ≫ f) =
      a ≫ tensorHomEquiv c N H f := by
  change tensorPresheafHomEquiv c M H
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        ((PresheafOfModules.sheafification (𝟙 (ringSheaf S).obj)).map
          ((tensorPresheafFunctor c).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  ext W m
  change ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv
    (changeOfRingsPresheaf.{vC, uC, u} c N) H f).app W
      ((ModuleCat.extendScalars (c.hom.app W).hom).map (a.val.app W)
        ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  rfl

private theorem tensorHomEquiv_naturality_right
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S)
    (M : SheafOfModules.{u} (ringSheaf A))
    {H H' : SheafOfModules.{u} (ringSheaf S)}
    (f : (tensorFunctor c).obj M ⟶ H) (b : H ⟶ H') :
    tensorHomEquiv c M H' (f ≫ b) =
      tensorHomEquiv c M H f ≫ (restriction c).map b := by
  change tensorPresheafHomEquiv c M H'
      ((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf S).obj)).homEquiv _ _
        (f ≫ b)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private noncomputable def tensorAdjunction
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) : tensorFunctor c ⊣ restriction c :=
  Adjunction.mkOfHomEquiv
    { homEquiv := tensorHomEquiv c
      homEquiv_naturality_left_symm := by
        intro M N H a g
        apply (tensorHomEquiv c M H).injective
        rw [Equiv.apply_symm_apply, tensorHomEquiv_naturality_left,
          Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f b ↦ tensorHomEquiv_naturality_right c _ f b }

private noncomputable def tensorUnit
    {D : Type uC} [Category.{vC} D] [EssentiallySmall.{u} D]
    {K : GrothendieckTopology D}
    [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {A S : Sheaf K CommRingCat.{u}} (c : A ⟶ S) (M : SheafOfModules.{u} (ringSheaf A)) :
    (underlying A).obj M ⟶ (underlying S).obj ((tensorFunctor c).obj M) :=
  (underlying A).map ((tensorAdjunction c).unit.app M)

section Pure
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- The canonical bilinear pairing, as a presheaf morphism.
Source: Stacks 03EK (blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private noncomputable def pureMap (M N : SheafOfModules.{u} (ringSheaf R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : SheafOfModules.{u} (ringSheaf R))
    {T T' : SheafOfModules.{u} (ringSheaf R)} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (A.val ◁ f.val) := by
  have h :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheaf R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : SheafOfModules.{u} (ringSheaf R)}
    (f : A' ⟶ A) (T : SheafOfModules.{u} (ringSheaf R)) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ▷ T.val) := by
  have h :=
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (ringSheaf R).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification F' G').hom =
      (tensorObjIsoSheafification F G).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf pairing into the sheaf tensor is natural in both modules.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private theorem pureMap_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    pureMap R F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ pureMap R F' G' := by
  let := monoidalCategory R
  have h : (tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg Hom.val h
  change (tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val ≫
      (tensorObjIsoSheafification F' G').inv.val at hval
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit
  have hn := η.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ η.app (F'.val ⊗ G'.val) =
    η.app (F.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val at hn
  unfold pureMap
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

/-- Tensor morphisms act componentwise on pure sections. Source: Stacks 03EK
(blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private theorem pure_map {M M' N N' : SheafOfModules.{u} (ringSheaf R)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W (pure R M N W m n) =
      pure R M' N' W (f.val.app W m) (g.val.app W n) := by
  exact congrArg (fun k ↦ k.app W (m ⊗ₜ[R.obj.obj W] n)) (pureMap_natural R f g)
end Pure

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {A B : Sheaf J CommRingCat.{u}} (c : A ⟶ B)

set_option maxHeartbeats 600000 in
-- Comparing both module-sheafification adjunctions involves nested tensor maps.
set_option maxHeartbeats 600000 in
-- Expand the two scalar extensions through the sheafification adjunction.
end SheafOfModules.CochainScalarConstruction

namespace SheafOfModules.CochainTensorComparison
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))


end SheafOfModules.CochainTensorComparison
