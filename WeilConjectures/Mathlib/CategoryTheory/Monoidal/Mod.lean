/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Module objects over a monoid object acting on its own category

For a monoid object `A` of a monoidal category `C`, acting on `C` through the tensor product,
this file records the action `A ⊗ X ⟶ X` of an `A`-module object `X` and its axioms in terms of
the tensor product (`CategoryTheory.Mod.act`), and the basic properties of the forgetful functor
`Mod.forget A : Mod C A ⥤ C`: it is faithful and reflects isomorphisms.

It also provides the image of a module object under a lax monoidal functor
(`CategoryTheory.Functor.mapMod`), which mathlib lists as a TODO in
`Mathlib.CategoryTheory.Monoidal.Mon`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

namespace Mod

variable {A : C} [MonObj A]

/-- The action `A ⊗ X ⟶ X` of a monoid object `A` on an `A`-module object `X` of `C`. -/
abbrev act (X : C) [ModObj A X] : A ⊗ X ⟶ X :=
  γ[A, X]

@[reassoc (attr := simp)]
lemma one_act (X : C) [ModObj A X] : η[A] ▷ X ≫ act X = (λ_ X).hom :=
  ModObj.one_smul (M := A) X

@[reassoc (attr := simp)]
lemma mul_act (X : C) [ModObj A X] :
    μ[A] ▷ X ≫ act X = (α_ A A X).hom ≫ A ◁ act X ≫ act X :=
  ModObj.mul_smul (M := A) X

@[reassoc]
lemma act_comp {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y) [IsModHom A f] :
    act X ≫ f = A ◁ f ≫ act Y :=
  IsModHom.smul_hom

@[reassoc (attr := simp)]
lemma act_hom {M N : Mod C A} (f : M ⟶ N) : act M.X ≫ f.hom = A ◁ f.hom ≫ act N.X :=
  IsModHom.smul_hom

variable (A) in
/-- An `A`-module structure on an object of `C`, from an action `A ⊗ X ⟶ X` satisfying the
axioms, stated in terms of the tensor product. -/
@[implicit_reducible]
def _root_.CategoryTheory.ModObj.mk' {X : C} (smul : A ⊗ X ⟶ X)
    (one_smul : η[A] ▷ X ≫ smul = (λ_ X).hom)
    (mul_smul : μ[A] ▷ X ≫ smul = (α_ A A X).hom ≫ A ◁ smul ≫ smul) : ModObj A X where
  smul := smul
  one_smul := one_smul
  mul_smul := mul_smul

lemma isModHom_of_act {X Y : C} [ModObj A X] [ModObj A Y] (f : X ⟶ Y)
    (h : act X ≫ f = A ◁ f ≫ act Y) : IsModHom A f :=
  ⟨h⟩

/-- A morphism of `A`-modules from a morphism commuting with the actions. -/
@[simps]
def homMk {M N : Mod C A} (f : M.X ⟶ N.X) (h : act M.X ≫ f = A ◁ f ≫ act N.X) : M ⟶ N :=
  letI := isModHom_of_act f h
  ⟨f⟩

instance : (forget (D := C) A).Faithful where
  map_injective h := Mod.hom_ext _ _ h

instance {M N : Mod C A} (f : M ⟶ N) [IsIso f] : IsIso f.hom :=
  inferInstanceAs (IsIso ((forget A).map f))

instance : (forget (D := C) A).ReflectsIsomorphisms where
  reflects {M N} f _ := by
    have : IsIso f.hom := ‹IsIso ((forget A).map f)›
    let e : M.X ≅ N.X := asIso f.hom
    have : IsModHom A e.hom := inferInstanceAs (IsModHom A f.hom)
    exact ⟨⟨⟨e.inv⟩, Mod.hom_ext _ _ e.hom_inv_id, Mod.hom_ext _ _ e.inv_hom_id⟩⟩

/-- An isomorphism of `A`-modules from an isomorphism commuting with the actions. -/
@[simps!]
def isoMk {M N : Mod C A} (e : M.X ≅ N.X) (h : act M.X ≫ e.hom = A ◁ e.hom ≫ act N.X) :
    M ≅ N where
  hom := homMk e.hom h
  inv := homMk e.inv (by
    rw [Iso.comp_inv_eq, Category.assoc, h, ← whiskerLeft_comp_assoc, Iso.inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  hom_inv_id := Mod.hom_ext _ _ e.hom_inv_id
  inv_hom_id := Mod.hom_ext _ _ e.inv_hom_id

end Mod

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (F : C ⥤ D) [F.LaxMonoidal]

open LaxMonoidal _root_.CategoryTheory.Mod

open scoped Obj

variable {A : C} [MonObj A]

/-- The image of an `A`-module object under a lax monoidal functor `F` is an `F A`-module
object, with the action `F A ⊗ F X ⟶ F (A ⊗ X) ⟶ F X`. -/
@[implicit_reducible]
def modObjObj (X : C) [ModObj A X] : ModObj (F.obj A) (F.obj X) :=
  .mk' _ (LaxMonoidal.μ F A X ≫ F.map (act X))
    (by
      rw [obj.η_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc,
        ← F.map_comp, one_act, left_unitality])
    (by
      rw [obj.μ_def, comp_whiskerRight, Category.assoc, μ_natural_left_assoc, ← F.map_comp,
        mul_act, F.map_comp, F.map_comp]
      simp only [associativity_assoc, MonoidalCategory.whiskerLeft_comp, Category.assoc,
        μ_natural_right_assoc])

variable (A) in
/-- A lax monoidal functor `F : C ⥤ D` takes `A`-module objects to `F A`-module objects. -/
@[simps]
def mapMod : Mod C A ⥤ Mod D (F.obj A) where
  obj M :=
    letI := F.modObjObj (A := A) M.X
    ⟨F.obj M.X⟩
  map {M N} f :=
    letI := F.modObjObj (A := A) M.X
    letI := F.modObjObj (A := A) N.X
    homMk (F.map f.hom) (by
      change (LaxMonoidal.μ F A M.X ≫ F.map (act M.X)) ≫ _ = _ ≫ LaxMonoidal.μ F A N.X ≫ F.map (act N.X)
      rw [Category.assoc, ← F.map_comp, act_hom, F.map_comp, μ_natural_right_assoc])

end Functor

end CategoryTheory

namespace CategoryTheory

namespace Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

lemma act_comap_obj {A B : C} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] (M : Mod C B) :
    act ((comap f).obj M).X = f ▷ M.X ≫ act M.X :=
  rfl

end Mod

namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

open _root_.CategoryTheory.Mod

open scoped Obj

lemma act_mapMod_obj (F : C ⥤ D) [F.LaxMonoidal] {A : C} [MonObj A] (M : Mod C A) :
    act ((F.mapMod A).obj M).X = LaxMonoidal.μ F A M.X ≫ F.map (act M.X) :=
  rfl

end Functor

instance IsMonHom.inv {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] {M N : C}
    [MonObj M] [MonObj N] (f : M ⟶ N) [IsIso f] [IsMonHom f] : IsMonHom (inv f) :=
  inferInstanceAs (IsMonHom (asIso f).inv)

namespace Adjunction

open Functor.LaxMonoidal Functor.OplaxMonoidal _root_.CategoryTheory.Mod

open scoped Obj

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  {A : C} {B : D} [MonObj A] [MonObj B] (φ : A ⟶ G.obj B) [IsMonHom φ]
  [IsIso ((adj.homEquiv _ _).symm φ)] [IsMonHom ((adj.homEquiv _ _).symm φ)]

/-- The left adjoint `M ↦ F M` on module objects, the `F A`-module `F M` viewed as a `B`-module
along the inverse of the adjoint `F A ⟶ B` of `φ : A ⟶ G B`. -/
noncomputable def modLeft : Mod C A ⥤ Mod D B :=
  F.mapMod A ⋙ comap (inv ((adj.homEquiv _ _).symm φ))

/-- The right adjoint `N ↦ G N` on module objects, the `G B`-module `G N` viewed as an
`A`-module along `φ : A ⟶ G B`. -/
@[nolint unusedArguments]
noncomputable def modRight (_adj : F ⊣ G) (φ : A ⟶ G.obj B) [IsMonHom φ] : Mod D B ⥤ Mod C A :=
  G.mapMod B ⋙ comap φ

variable {adj φ} in
/-- A morphism `F M ⟶ N` is `B`-linear iff `F (A ⊗ M) ⟶ F M ⟶ N` agrees with
`F (A ⊗ M) ⟶ F A ⊗ F M ⟶ B ⊗ N ⟶ N`. -/
lemma modLeft_linear_iff {M : Mod C A} {N : Mod D B} (f : F.obj M.X ⟶ N.X) :
    act ((adj.modLeft φ).obj M).X ≫ f = B ◁ f ≫ act N.X ↔
      F.map (act M.X) ≫ f = δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ f) ≫ act N.X := by
  set ψ := (adj.homEquiv _ _).symm φ
  change (inv ψ ▷ F.obj M.X ≫ Functor.LaxMonoidal.μ F A M.X ≫ F.map (act M.X)) ≫ f = _ ↔ _
  constructor
  · intro h
    have h' := congrArg (fun k ↦ δ F A M.X ≫ ψ ▷ F.obj M.X ≫ k) h
    simpa only [Category.assoc, ← comp_whiskerRight_assoc, IsIso.hom_inv_id, id_whiskerRight,
      Category.id_comp, Functor.Monoidal.δ_μ_assoc, tensorHom_def] using h'
  · intro h
    rw [Category.assoc, Category.assoc, h, Functor.Monoidal.μ_δ_assoc, tensorHom_def]
    simp only [Category.assoc, ← comp_whiskerRight_assoc, IsIso.inv_hom_id, id_whiskerRight,
      Category.id_comp]

variable {adj φ} in
/-- A morphism `M ⟶ G N` is `A`-linear iff its adjoint `F M ⟶ N` satisfies the condition of
`CategoryTheory.Adjunction.modLeft_linear_iff`. -/
lemma modRight_linear_iff {M : Mod C A} {N : Mod D B} (g : M.X ⟶ G.obj N.X) :
    act M.X ≫ g = A ◁ g ≫ act ((adj.modRight φ).obj N).X ↔
      F.map (act M.X) ≫ (adj.homEquiv _ _).symm g =
        δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ (adj.homEquiv _ _).symm g) ≫ act N.X := by
  change act M.X ≫ g = A ◁ g ≫ φ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G B N.X ≫ G.map (act N.X) ↔ _
  rw [← (adj.homEquiv _ _).symm.injective.eq_iff, adj.homEquiv_naturality_left_symm]
  have key : (adj.homEquiv _ _).symm (A ◁ g ≫ φ ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G B N.X ≫
      G.map (act N.X)) = δ F A M.X ≫ ((adj.homEquiv _ _).symm φ ⊗ₘ
        (adj.homEquiv _ _).symm g) ≫ act N.X := by
    simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      Adjunction.counit_naturality, Adjunction.map_μ_comp_counit_app_tensor_assoc]
    rw [← δ_natural_left_assoc, ← δ_natural_right_assoc]
    simp only [tensorHom_def, comp_whiskerRight, MonoidalCategory.whiskerLeft_comp, Category.assoc,
      whisker_exchange_assoc]
  rw [key]

/-- **A monoidal adjunction lifts to module objects**: for a monoidal adjunction `F ⊣ G` with `F`
strong monoidal and a monoid morphism `φ : A ⟶ G B` whose adjoint `F A ⟶ B` is invertible,
`F` and `G` induce an adjunction between `A`-modules and `B`-modules. -/
noncomputable def modAdjunction : adj.modLeft φ ⊣ adj.modRight φ :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N :=
        { toFun f := homMk (M := M) (N := (adj.modRight φ).obj N) (adj.homEquiv _ _ f.hom)
            ((modRight_linear_iff _).2 (by
              rw [Equiv.symm_apply_apply]
              exact (modLeft_linear_iff _).1 (act_hom f)))
          invFun g := homMk (M := (adj.modLeft φ).obj M) (N := N) ((adj.homEquiv _ _).symm g.hom)
            ((modLeft_linear_iff _).2 ((modRight_linear_iff _).1 (act_hom g)))
          left_inv f := Mod.hom_ext _ _ (Equiv.symm_apply_apply _ _)
          right_inv g := Mod.hom_ext _ _ (Equiv.apply_symm_apply _ _) }
      homEquiv_naturality_left_symm f g :=
        Mod.hom_ext _ _ (adj.homEquiv_naturality_left_symm f.hom g.hom)
      homEquiv_naturality_right f g :=
        Mod.hom_ext _ _ (adj.homEquiv_naturality_right f.hom g.hom) }

lemma modAdjunction_homEquiv_apply_hom {M : Mod C A} {N : Mod D B}
    (f : (adj.modLeft φ).obj M ⟶ N) :
    ((adj.modAdjunction φ).homEquiv M N f).hom = adj.homEquiv _ _ f.hom := by
  simp [modAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

end Adjunction

end CategoryTheory
