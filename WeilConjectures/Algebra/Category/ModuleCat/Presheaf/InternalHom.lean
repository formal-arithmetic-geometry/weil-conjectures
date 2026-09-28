/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# The internal hom of presheaves of modules

Let `R : Cᵒᵖ ⥤ CommRingCat` be a presheaf of commutative rings on a category `C`. For presheaves
of modules `M` and `N` over `R`, we define the presheaf of modules `homObj M N` which sends `U`
to the `R(U)`-module of morphisms between the restrictions of `M` and `N` to `Over U`. A section
`r` of `R` over `U` acts on such a morphism by post-composition with multiplication by the
restrictions of `r`. This is the presheaf of modules analogue of `presheafHom`.

## Main definitions

* `PresheafOfModules.homObj M N`: the internal hom presheaf `U ↦ Hom_{R|_U}(M|_U, N|_U)`.
* `PresheafOfModules.homObjMap`: its functoriality, contravariant in `M` and covariant in `N`.
* `PresheafOfModules.homFunctor`: the internal hom bifunctor.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The restriction of a presheaf of modules to `Over U`. -/
abbrev restrictOver (U : C) (M : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) :
    PresheafOfModules.{v} ((Over.forget U).op ⋙ R ⋙ forget₂ _ _) :=
  (pushforward₀ (Over.forget U) (R ⋙ forget₂ _ _)).obj M

variable (U : C) (M N : PresheafOfModules.{v} (R ⋙ forget₂ _ _))

/-- Multiplication by the restriction of a section `r` of `R` over `U`, as an endomorphism of the
restriction of `N` to `Over U`. -/
noncomputable def overSMul (r : R.obj (op U)) : restrictOver U N ⟶ restrictOver U N where
  app W := ModuleCat.ofHom
    (LinearMap.lsmul (R.obj (op W.unop.left)) (N.obj (op W.unop.left)) (R.map W.unop.hom.op r))
  naturality {W W'} f := by
    ext x
    revert x
    change ∀ x : N.obj (op W.unop.left), R.map W'.unop.hom.op r •
      (N.map f.unop.left.op x : N.obj (op W'.unop.left)) =
        N.map f.unop.left.op (R.map W.unop.hom.op r • x)
    intro x
    rw [N.map_smul]
    congr 1
    change _ = (R.map W.unop.hom.op ≫ R.map f.unop.left.op) r
    rw [← R.map_comp, ← op_comp, Over.w]

@[simp]
lemma overSMul_app_apply (r : R.obj (op U)) (W : (Over U)ᵒᵖ) (x : N.obj (op W.unop.left)) :
    (overSMul U N r).app W x = R.map W.unop.hom.op r • x :=
  rfl

/-- Multiplication by sections of `R` over `U`, as a ring homomorphism to the endomorphisms of the
restriction of `N` to `Over U`. -/
noncomputable def overSMulHom : R.obj (op U) →+* End (restrictOver U N) where
  toFun := overSMul U N
  map_one' := by
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : N.obj (op W.unop.left), R.map W.unop.hom.op 1 • x = x
    intro x
    rw [map_one, one_smul]
  map_mul' r s := by
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : N.obj (op W.unop.left), R.map W.unop.hom.op (r * s) • x =
      R.map W.unop.hom.op r • R.map W.unop.hom.op s • x
    intro x
    rw [map_mul, mul_smul]
  map_zero' := by
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : N.obj (op W.unop.left), R.map W.unop.hom.op 0 • x = 0
    intro x
    rw [map_zero, zero_smul]
  map_add' r s := by
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : N.obj (op W.unop.left), R.map W.unop.hom.op (r + s) • x =
      R.map W.unop.hom.op r • x + R.map W.unop.hom.op s • x
    intro x
    rw [map_add, add_smul]

variable {N} in
@[reassoc]
lemma overSMul_naturality {N' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} (g : N ⟶ N')
    (r : R.obj (op U)) :
    (pushforward₀ (Over.forget U) _).map g ≫ overSMul U N' r =
      overSMul U N r ≫ (pushforward₀ (Over.forget U) _).map g := by
  ext W x
  exact ((g.app (op W.unop.left)).hom.map_smul _ x).symm

/-- The `R(U)`-module structure on morphisms between restrictions to `Over U`: a section `r` acts
by post-composition with multiplication by the restrictions of `r`. -/
noncomputable instance : Module (R.obj (op U)) (restrictOver U M ⟶ restrictOver U N) :=
  Module.compHom _ (overSMulHom U N)

lemma smul_def (r : R.obj (op U)) (φ : restrictOver U M ⟶ restrictOver U N) :
    r • φ = φ ≫ overSMul U N r :=
  rfl
variable {U N M}

/-- Restriction of a morphism between restrictions to `Over U` along `g : V ⟶ U`, using
`Over.map g ⋙ Over.forget U = Over.forget V`. -/
noncomputable def restrictOverMap {V : C} (g : V ⟶ U)
    (φ : restrictOver U M ⟶ restrictOver U N) : restrictOver V M ⟶ restrictOver V N :=
  (pushforward₀ (Over.map g) _).map φ

@[simp]
lemma restrictOverMap_app {V : C} (g : V ⟶ U) (φ : restrictOver U M ⟶ restrictOver U N)
    (W : (Over V)ᵒᵖ) : (restrictOverMap g φ).app W = φ.app (op ((Over.map g).obj W.unop)) :=
  rfl

variable (N) in
lemma overSMul_app_map_obj {V : C} (g : V ⟶ U) (r : R.obj (op U)) (W : (Over V)ᵒᵖ) :
    (overSMul U N r).app (op ((Over.map g).obj W.unop)) = (overSMul V N (R.map g.op r)).app W := by
  change ModuleCat.ofHom (LinearMap.lsmul (R.obj (op W.unop.left)) (N.obj (op W.unop.left))
      (R.map (W.unop.hom ≫ g).op r)) =
    ModuleCat.ofHom (LinearMap.lsmul (R.obj (op W.unop.left)) (N.obj (op W.unop.left))
      (R.map W.unop.hom.op (R.map g.op r)))
  rw [op_comp, R.map_comp, CommRingCat.comp_apply]

variable (M N)

/-- The internal hom presheaf of modules `U ↦ Hom_{R|_U}(M|_U, N|_U)`. -/
noncomputable def homObj : PresheafOfModules.{max u₁ v₁ v} (R ⋙ forget₂ _ _) where
  obj X := ModuleCat.of (R.obj (op X.unop)) (restrictOver X.unop M ⟶ restrictOver X.unop N)
  map {X Y} g := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map g).hom).obj
      (ModuleCat.of (R.obj (op Y.unop)) (restrictOver Y.unop M ⟶ restrictOver Y.unop N)))
    { toFun φ := restrictOverMap g.unop φ
      map_add' _ _ := rfl
      map_smul' r φ := by
        change restrictOverMap g.unop (φ ≫ overSMul _ N r) =
          restrictOverMap g.unop φ ≫ overSMul _ N (R.map g r)
        refine hom_ext fun W ↦ ?_
        exact congrArg (φ.app _ ≫ ·) (overSMul_app_map_obj N g.unop r W) }
  map_id X := by
    ext φ
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : M.obj (op W.unop.left),
      φ.app (op ((Over.map (𝟙 X.unop)).obj W.unop)) x = φ.app W x
    intro x
    have h (P : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) (y : P.obj (op W.unop.left)) :
        (restrictOver X.unop P).map ((Over.mapId X.unop).hom.app W.unop).op y = y := by
      change P.map (𝟙 (op W.unop.left)) y = y
      simp
      rfl
    have := naturality_apply φ ((Over.mapId X.unop).hom.app W.unop).op x
    rw [h] at this
    exact this.trans (h N _)
  map_comp {X Y Z} f g := by
    ext φ
    refine hom_ext fun W ↦ ?_
    ext x
    revert x
    change ∀ x : M.obj (op W.unop.left),
      φ.app (op ((Over.map (g.unop ≫ f.unop)).obj W.unop)) x =
        φ.app (op ((Over.map f.unop).obj ((Over.map g.unop).obj W.unop))) x
    intro x
    have h (P : PresheafOfModules.{v} (R ⋙ forget₂ _ _)) (y : P.obj (op W.unop.left)) :
        (restrictOver X.unop P).map ((Over.mapComp g.unop f.unop).hom.app W.unop).op y = y := by
      change P.map (𝟙 (op W.unop.left)) y = y
      simp
      rfl
    have := naturality_apply φ ((Over.mapComp g.unop f.unop).hom.app W.unop).op x
    rw [h] at this
    exact this.trans (h N _)

variable {M N}

lemma homObj_map_apply {X Y : Cᵒᵖ} (g : X ⟶ Y) (φ : (homObj M N).obj X) :
    (homObj M N).map g φ = restrictOverMap g.unop φ :=
  rfl

variable {M' N' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)}

/-- The functoriality of `homObj M N`: contravariant in `M` and covariant in `N`. -/
noncomputable def homObjMap (f : M' ⟶ M) (g : N ⟶ N') : homObj M N ⟶ homObj M' N' where
  app X := ModuleCat.ofHom
    (X := ModuleCat.of (R.obj (op X.unop)) (restrictOver X.unop M ⟶ restrictOver X.unop N))
    (Y := ModuleCat.of (R.obj (op X.unop)) (restrictOver X.unop M' ⟶ restrictOver X.unop N'))
    { toFun φ := (pushforward₀ (Over.forget X.unop) _).map f ≫ φ ≫
        (pushforward₀ (Over.forget X.unop) _).map g
      map_add' _ _ := by simp
      map_smul' r φ := by
        simp only [smul_def, Category.assoc, overSMul_naturality, RingHom.id_apply] }
  naturality _ := by ext; rfl

lemma homObjMap_app_apply (f : M' ⟶ M) (g : N ⟶ N') (X : Cᵒᵖ)
    (φ : restrictOver X.unop M ⟶ restrictOver X.unop N) :
    (homObjMap f g).app X φ = (pushforward₀ (Over.forget X.unop) _).map f ≫ φ ≫
      (pushforward₀ (Over.forget X.unop) _).map g :=
  rfl

@[simp]
lemma homObjMap_id : homObjMap (𝟙 M) (𝟙 N) = 𝟙 (homObj M N) := by
  ext X φ
  revert φ
  change ∀ φ : restrictOver X.unop M ⟶ restrictOver X.unop N,
    (pushforward₀ _ _).map (𝟙 M) ≫ φ ≫ (pushforward₀ _ _).map (𝟙 N) = φ
  simp

@[simp]
lemma homObjMap_comp {M'' N'' : PresheafOfModules.{v} (R ⋙ forget₂ _ _)} (f : M' ⟶ M)
    (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    homObjMap (f' ≫ f) (g ≫ g') = homObjMap f g ≫ homObjMap f' g' := by
  ext X φ
  revert φ
  change ∀ φ : restrictOver X.unop M ⟶ restrictOver X.unop N,
    (pushforward₀ _ _).map (f' ≫ f) ≫ φ ≫ (pushforward₀ _ _).map (g ≫ g') =
    (pushforward₀ _ _).map f' ≫ ((pushforward₀ _ _).map f ≫ φ ≫ (pushforward₀ _ _).map g) ≫
      (pushforward₀ _ _).map g'
  simp

variable (R) in
/-- The internal hom bifunctor on presheaves of modules, `(M, N) ↦ homObj M N`. -/
@[simps]
noncomputable def homFunctor :
    (PresheafOfModules.{v} (R ⋙ forget₂ _ _))ᵒᵖ ⥤
      PresheafOfModules.{v} (R ⋙ forget₂ _ _) ⥤
        PresheafOfModules.{max u₁ v₁ v} (R ⋙ forget₂ _ _) where
  obj M :=
    { obj N := homObj M.unop N
      map g := homObjMap (𝟙 M.unop) g
      map_comp g g' := by rw [← homObjMap_comp, Category.id_comp] }
  map f :=
    { app N := homObjMap f.unop (𝟙 N)
      naturality N N' g := by
        dsimp
        rw [← homObjMap_comp, ← homObjMap_comp, Category.id_comp, Category.comp_id,
          Category.id_comp, Category.comp_id] }
  map_comp f f' := by
    ext N : 2
    dsimp
    rw [← homObjMap_comp, Category.comp_id]

end PresheafOfModules
