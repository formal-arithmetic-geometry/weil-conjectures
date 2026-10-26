/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import WeilConjectures.CategoryTheory.Adjunction.EndoFamily

/-!
# Scalar multiplications on sheaves of modules

Let `R` be a commutative ring and `F` a sheaf of `R`-modules on a site `(C, J)`.

* `CategoryTheory.Sheaf.smulEnd r F : F ⟶ F` is the multiplication by `r ∈ R`; it commutes with
  all morphisms of sheaves of modules (`CategoryTheory.Sheaf.comp_smulEnd`).
* `CategoryTheory.Sheaf.isoOfSheafComposeForget₂Iso`: an isomorphism of the underlying abelian
  sheaves which commutes with the multiplications by all `r ∈ R` is an isomorphism of sheaves of
  `R`-modules.
* `CategoryTheory.Sheaf.constantSheaf_map_smul`: the constant sheaf functor sends the
  multiplication by `r` to the multiplication by `r`.
* `CategoryTheory.Sheaf.bijective_constantSheaf_hom_app`: the constant sheaf `R` corepresents
  the sections over a terminal object, through its unit section.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type w} [CommRing R]

/-- The multiplication by `r ∈ R` on a sheaf of `R`-modules. -/
def smulEnd (r : R) (F : Sheaf J (ModuleCat.{w} R)) : F ⟶ F :=
  ⟨{ app U := ModuleCat.ofHom (r • LinearMap.id)
     naturality U V f := by
       ext x
       exact ((F.obj.map f).hom.map_smul r x).symm }⟩

@[simp]
lemma smulEnd_hom_app_apply (r : R) (F : Sheaf J (ModuleCat.{w} R)) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (smulEnd r F).hom.app U x = r • x :=
  rfl

/-- The multiplication by `r` commutes with all morphisms of sheaves of `R`-modules. -/
@[reassoc]
lemma comp_smulEnd (r : R) {F G : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ G) :
    f ≫ smulEnd r G = smulEnd r F ≫ f := by
  ext U x
  exact ((f.hom.app U).hom.map_smul r x).symm

/-- An isomorphism of the underlying abelian sheaves of two sheaves of `R`-modules which
commutes with the multiplications by all `r ∈ R` is an isomorphism of sheaves of modules. -/
def isoOfSheafComposeForget₂Iso [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
    {F G : Sheaf J (ModuleCat.{w} R)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj G)
    (h : ∀ r : R, (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).map
        (smulEnd r F) ≫ e.hom =
      e.hom ≫ (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).map
        (smulEnd r G)) : F ≅ G :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso
    (NatIso.ofComponents
      (fun U ↦ LinearEquiv.toModuleIso
        { toFun x := e.hom.hom.app U x
          invFun x := e.inv.hom.app U x
          map_add' x y := (e.hom.hom.app U).hom.map_add x y
          map_smul' r x := congrArg (fun k ↦ k.hom.app U x) (h r)
          left_inv x := congrArg (fun k ↦ k.hom.app U x) e.hom_inv_id
          right_inv x := congrArg (fun k ↦ k.hom.app U x) e.inv_hom_id })
      fun {U V} f ↦ by
        ext x
        exact congrArg (fun k ↦ k x) (e.hom.hom.naturality f))

@[simp]
lemma isoOfSheafComposeForget₂Iso_hom_hom_app_apply
    [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]
    {F G : Sheaf J (ModuleCat.{w} R)}
    (e : (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F ≅
      (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj G)
    (h : ∀ r : R, (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).map
        (smulEnd r F) ≫ e.hom =
      e.hom ≫ (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).map
        (smulEnd r G)) (U : Cᵒᵖ) (x : F.obj.obj U) :
    (isoOfSheafComposeForget₂Iso e h).hom.hom.app U x = e.hom.hom.app U x :=
  rfl

/-- A left adjoint between categories of sheaves of `R`-modules whose right adjoint commutes
with the multiplications by `r` commutes with them. -/
lemma map_smulEnd_of_adjunction {C' : Type*} [Category* C'] {K : GrothendieckTopology C'}
    {L : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R)}
    {G : Sheaf K (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R)} (adj : L ⊣ G)
    (hG : ∀ (r : R) (F : Sheaf K (ModuleCat.{w} R)), G.map (smulEnd r F) = smulEnd r (G.obj F))
    (r : R) (F : Sheaf J (ModuleCat.{w} R)) : L.map (smulEnd r F) = smulEnd r (L.obj F) :=
  adj.map_eq_of_rightAdjoint_map_eq (fun F ↦ smulEnd r F) (fun F ↦ smulEnd r F)
    (fun f ↦ comp_smulEnd r f) (hG r) F

section Constant

variable (J) [HasWeakSheafify J (ModuleCat.{w} R)] {T : C}

/-- The constant sheaf functor sends the multiplication by `r` on an `R`-module `M` to the
multiplication by `r` on the constant sheaf. -/
lemma constantSheaf_map_smul (hT : IsTerminal T) (r : R) (M : ModuleCat.{w} R) :
    (constantSheaf J (ModuleCat.{w} R)).map (r • 𝟙 M) =
      smulEnd r ((constantSheaf J (ModuleCat.{w} R)).obj M) :=
  (constantSheafAdj J (ModuleCat.{w} R) hT).map_eq_of_rightAdjoint_map_eq (fun M ↦ r • 𝟙 M)
    (fun F ↦ smulEnd r F) (fun f ↦ by rw [Linear.comp_smul, Linear.smul_comp]; simp)
    (fun F ↦ by ext x; rfl) M

/-- The unit section of the constant sheaf `R`: the image of `1 ∈ R` under the unit of the
adjunction between the constant sheaf functor and the sections over a terminal object `T`. -/
noncomputable def constantSheafUnitSection (hT : IsTerminal T) :
    ((constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R)).obj.obj (op T) :=
  (constantSheafAdj J (ModuleCat.{w} R) hT).unit.app (ModuleCat.of R R) (1 : R)

/-- **The constant sheaf `R` corepresents the sections over a terminal object**: a morphism out
of it is determined by the image of its unit section, which can be arbitrary. -/
lemma bijective_constantSheaf_hom_app (hT : IsTerminal T) (G : Sheaf J (ModuleCat.{w} R)) :
    Function.Bijective
      (fun f : (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ G ↦
        f.hom.app (op T) (constantSheafUnitSection J hT)) := by
  let e : ((ModuleCat.of R R) ⟶ G.obj.obj (op T)) ≃ G.obj.obj (op T) :=
    ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf R R _).toEquiv
  have h : (fun f : (constantSheaf J (ModuleCat.{w} R)).obj (ModuleCat.of R R) ⟶ G ↦
      f.hom.app (op T) (constantSheafUnitSection J hT)) =
      e ∘ (constantSheafAdj J (ModuleCat.{w} R) hT).homEquiv _ _ := by
    funext f
    rfl
  rw [h]
  exact e.bijective.comp (Equiv.bijective _)

end Constant

end CategoryTheory.Sheaf
