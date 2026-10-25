/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Center.Linear
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv

/-!
# Module objects over a commutative ring object are linear over its global sections

Let `C` be a braided monoidal preadditive category and `R` a commutative algebra object of `C`.
A global section `s : 𝟙_ C ⟶ R` acts on every `R`-module object `M` by
`M ≅ 𝟙 ⊗ M ⟶ R ⊗ M ⟶ M` (`CategoryTheory.Mod.smulHom`). By commutativity of `R` this is a
morphism of module objects, natural in `M`, so that it is an element of the center of the
category `Mod C R`, and this defines a ring homomorphism `Γ R →+* CatCenter (Mod C R)`
(`CategoryTheory.Mod.toCatCenter`). Hence, for a ring homomorphism `φ : K →+* Γ R`, the category
`Mod C R` is `K`-linear (`CategoryTheory.Mod.linearOfRingHom`), with `a • f = f ≫ (φ a) • -`.

The change of coefficients functors are linear:

* `CategoryTheory.Mod.linear_comap`: the restriction of scalars along a morphism of algebra objects
  `f : R ⟶ S` is `K`-linear when the `K`-actions on `R` and `S` are compatible with `f`;
* `CategoryTheory.Mod.linear_mapMod`: the image `G.mapMod R : Mod C R ⥤ Mod D (G R)` of module
  objects under an additive lax monoidal functor `G` is `K`-linear, `K` acting on `G R` through
  `Γ R →+* Γ (G R)` (when `G R` is commutative);
* `CategoryTheory.Mod.linear_mapMod_comp_comap`: `G.mapMod R` followed by restriction of scalars
  along `f : S ⟶ G R` is `K`-linear when `f` sends the action of `K` on `S` to the image of its
  action on `R`. This is the shape of pushforwards of module objects in ringed topoi.

A criterion for the last hypothesis: for a monoidal adjunction `F ⊣ G` and a monoidal natural
transformation `τ : P ⋙ F ⟶ Q`, the mate `P ⟶ Q ⋙ G` of `τ` sends the global sections
`ε ≫ P s` to `ε ≫ G (ε ≫ Q s)` (`CategoryTheory.Adjunction.ε_comp_map_comp_unit_app_comp_map`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Preadditive

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Action

variable {R : C} [MonObj R]

/-- The action `M ≅ 𝟙 ⊗ M ⟶ R ⊗ M ⟶ M` of a global section `s : 𝟙 ⟶ R` on an `R`-module object
`M`. -/
def smulHom (s : Γ R) (M : Mod C R) : M.X ⟶ M.X :=
  (λ_ M.X).inv ≫ s.hom ▷ M.X ≫ act M.X

lemma smulHom_naturality (s : Γ R) {M N : Mod C R} (f : M ⟶ N) :
    smulHom s M ≫ f.hom = f.hom ≫ smulHom s N := by
  rw [smulHom, smulHom, Category.assoc, Category.assoc, act_hom, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

@[simp]
lemma smulHom_one (M : Mod C R) : smulHom 1 M = 𝟙 M.X := by
  rw [smulHom, Γ.one_hom, one_act, Iso.inv_hom_id]

lemma smulHom_mul (s t : Γ R) (M : Mod C R) :
    smulHom (s * t) M = smulHom t M ≫ smulHom s M := by
  rw [smulHom, smulHom, smulHom, Γ.mul_hom, tensorHom_def, comp_whiskerRight,
    comp_whiskerRight, Category.assoc, Category.assoc, mul_act, ← comp_whiskerRight_assoc,
    ← whisker_exchange, Category.assoc, Category.assoc,
    leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  monoidal

/-- The action of a global section on a module obtained by restriction of scalars along a morphism
of algebra objects `f : R ⟶ S` is the action of the image of the global section under `f`. -/
lemma smulHom_comap_obj {S : C} [MonObj S] (f : R ⟶ S) [IsMonHom f] (s : Γ R) (M : Mod C S) :
    smulHom s ((comap f).obj M) = smulHom (Γ.mapMonoidHom f s) M := by
  rw [smulHom, smulHom, act_comap_obj, Γ.mapMonoidHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Γ.hom_ofHom, comp_whiskerRight, Category.assoc]
  rfl

end Action

section MapMod

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (G : C ⥤ D) [G.LaxMonoidal]
  {R : C} [MonObj R]

open scoped Obj

/-- The image of the action of a global section `s` on `M` under a lax monoidal functor `G` is
the action of the global section `ε ≫ G s` of `G R` on `G M`. -/
lemma smulHom_mapMod_obj (s : Γ R) (M : Mod C R) :
    smulHom (Γ.mapFunctorMonoidHom G s) ((G.mapMod R).obj M) = G.map (smulHom s M) := by
  rw [smulHom, smulHom, Γ.mapFunctorMonoidHom_hom, Functor.act_mapMod_obj, comp_whiskerRight,
    Category.assoc, Functor.map_comp, Functor.map_comp,
    ← Functor.LaxMonoidal.left_unitality_inv_assoc, ← Functor.LaxMonoidal.μ_natural_left_assoc]
  rfl

end MapMod

section Comm

variable [BraidedCategory C] {R : C} [MonObj R] [IsCommMonObj R]

/-- A global section of a commutative algebra object is central: multiplying by it on the left
or on the right agree. -/
lemma leftUnitor_inv_comp_whiskerRight_comp_mul (s : Γ R) :
    (λ_ R).inv ≫ s.hom ▷ R ≫ μ = (ρ_ R).inv ≫ R ◁ s.hom ≫ μ := by
  conv_rhs => rw [← IsCommMonObj.mul_comm R, BraidedCategory.braiding_naturality_right_assoc,
    rightUnitor_inv_braiding_assoc]

/-- The action of a global section of a commutative algebra object `R` on an `R`-module object
commutes with the action of `R`. -/
lemma act_comp_smulHom (s : Γ R) (M : Mod C R) :
    act M.X ≫ smulHom s M = R ◁ smulHom s M ≫ act M.X := by
  have h : R ◁ act M.X ≫ act M.X = (α_ R R M.X).inv ≫ μ ▷ M.X ≫ act M.X := by
    rw [mul_act, Iso.inv_hom_id_assoc]
  have hc := congrArg (· ▷ M.X) (leftUnitor_inv_comp_whiskerRight_comp_mul s)
  simp only [comp_whiskerRight] at hc
  rw [smulHom, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    MonoidalCategory.whiskerLeft_comp_assoc, MonoidalCategory.whiskerLeft_comp_assoc, h]
  calc _ = ((λ_ R).inv ▷ M.X ≫ (s.hom ▷ R) ▷ M.X ≫ μ ▷ M.X) ≫ act M.X := by monoidal
    _ = ((ρ_ R).inv ▷ M.X ≫ (R ◁ s.hom) ▷ M.X ≫ μ ▷ M.X) ≫ act M.X := by rw [hc]
    _ = _ := by monoidal

/-- The action of a global section `s` of a commutative algebra object `R` on an `R`-module
object `M`, as an endomorphism of module objects. -/
def smulEnd (s : Γ R) (M : Mod C R) : M ⟶ M :=
  homMk (smulHom s M) (act_comp_smulHom s M)

@[simp]
lemma smulEnd_hom (s : Γ R) (M : Mod C R) : (smulEnd s M).hom = smulHom s M :=
  rfl

variable [Preadditive C] [MonoidalPreadditive C]

@[simp]
lemma smulHom_zero (M : Mod C R) : smulHom 0 M = 0 := by
  rw [smulHom, Γ.zero_hom, MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp,
    Limits.comp_zero]

lemma smulHom_add (s t : Γ R) (M : Mod C R) :
    smulHom (s + t) M = smulHom s M + smulHom t M := by
  rw [smulHom, smulHom, smulHom, Γ.add_hom, MonoidalPreadditive.add_whiskerRight, add_comp,
    comp_add]

variable (R) in
/-- The global sections of a commutative algebra object `R` act on the category of `R`-module
objects: a ring homomorphism to the center of `Mod C R`. -/
def toCatCenter : Γ R →+* CatCenter (Mod C R) where
  toFun s :=
    { app M := smulEnd s M
      naturality _ _ f := Mod.hom_ext _ _ (smulHom_naturality s f).symm }
  map_one' := CatCenter.ext _ _ fun M ↦ by
    refine Mod.hom_ext _ _ ?_
    exact smulHom_one M
  map_mul' s t := CatCenter.ext _ _ fun M ↦ by
    refine Mod.hom_ext _ _ ?_
    rw [CatCenter.mul_app, mul_comm s t]
    exact smulHom_mul t s M
  map_zero' := CatCenter.ext _ _ fun M ↦ by
    refine Mod.hom_ext _ _ ?_
    exact smulHom_zero M
  map_add' s t := CatCenter.ext _ _ fun M ↦ by
    refine Mod.hom_ext _ _ ?_
    exact smulHom_add s t M

@[simp]
lemma toCatCenter_app (s : Γ R) (M : Mod C R) : (toCatCenter R s).app M = smulEnd s M :=
  rfl

variable {K : Type*} [Ring K]

/-- The `K`-linear structure on the category of module objects over a commutative algebra object
`R`, given a ring homomorphism `φ : K →+* Γ R` to the global sections of `R`: `a : K` acts by
the action of the global section `φ a`. -/
@[instance_reducible]
noncomputable def linearOfRingHom (φ : K →+* Γ R) : Linear K (Mod C R) :=
  Linear.ofRingMorphism ((toCatCenter R).comp φ)

lemma linearOfRingHom_smul_hom (φ : K →+* Γ R) (a : K) {M N : Mod C R} (f : M ⟶ N) :
    letI := linearOfRingHom φ
    (a • f).hom = f.hom ≫ smulHom (φ a) N :=
  congrArg Mod.Hom.hom (Linear.smulOfRingMorphism_smul_eq' ((toCatCenter R).comp φ) a f)

lemma linearOfRingHom_smul_id (φ : K →+* Γ R) (a : K) (M : Mod C R) :
    letI := linearOfRingHom φ
    a • 𝟙 M = smulEnd (φ a) M :=
  Mod.hom_ext _ _ ((linearOfRingHom_smul_hom φ a (𝟙 M)).trans (Category.id_comp _))

variable (R) in
/-- The category of module objects over a commutative algebra object `R` is linear over the
global sections of `R`. -/
@[instance_reducible]
noncomputable def linearGlobalSections : Linear (Γ R) (Mod C R) :=
  linearOfRingHom (RingHom.id _)

/-- A functor `F : Mod C R ⥤ Mod D S` of categories of module objects over commutative algebra
objects, `K`-linear for `K →+* Γ R` and `K →+* Γ S`, is `K`-linear as soon as it sends the action
of `φ a` to the action of `ψ a`. -/
lemma functor_linear_of_map_smulEnd {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    [BraidedCategory D] [Preadditive D] [MonoidalPreadditive D] {S : D} [MonObj S]
    [IsCommMonObj S] (F : Mod C R ⥤ Mod D S) (φ : K →+* Γ R) (ψ : K →+* Γ S)
    (h : ∀ (a : K) (M : Mod C R), (F.map (smulEnd (φ a) M)).hom = smulHom (ψ a) (F.obj M)) :
    letI := linearOfRingHom φ
    letI := linearOfRingHom ψ
    F.Linear K := by
  let _ := linearOfRingHom φ
  let _ := linearOfRingHom ψ
  refine (Functor.linear_iff K F).2 fun M a ↦ ?_
  rw [linearOfRingHom_smul_id, linearOfRingHom_smul_id]
  exact Mod.hom_ext _ _ (h a M)

/-- Restriction of scalars along a morphism of commutative algebra objects `f : R ⟶ S` is
`K`-linear, for compatible ring homomorphisms `K →+* Γ R` and `K →+* Γ S`. -/
lemma linear_comap {S : C} [MonObj S] [IsCommMonObj S] (f : R ⟶ S) [IsMonHom f]
    (φ : K →+* Γ R) (ψ : K →+* Γ S) (h : ∀ a, Γ.map f (φ a) = ψ a) :
    letI := linearOfRingHom φ
    letI := linearOfRingHom ψ
    (comap (D := C) f).Linear K :=
  functor_linear_of_map_smulEnd _ ψ φ fun a M ↦ by
    rw [smulHom_comap_obj, ← h a]
    rfl

section MapMod

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D] [Preadditive D]
  [MonoidalPreadditive D] (G : C ⥤ D) [G.LaxMonoidal]

open scoped Obj

/-- The image of module objects under a lax monoidal functor `G`, followed by restriction of
scalars along a morphism of commutative algebra objects `f : S ⟶ G R`, is `K`-linear, for ring
homomorphisms `φ : K →+* Γ R` and `ψ : K →+* Γ S` such that `f` sends the global section `ψ a`
to the image `ε ≫ G (φ a)` of `φ a`. -/
lemma linear_mapMod_comp_comap {S : D} [MonObj S] [IsCommMonObj S] (f : S ⟶ G.obj R)
    [IsMonHom f] (φ : K →+* Γ R) (ψ : K →+* Γ S)
    (h : ∀ a, (ψ a).hom ≫ f = Functor.LaxMonoidal.ε G ≫ G.map (φ a).hom) :
    letI := linearOfRingHom φ
    letI := linearOfRingHom ψ
    (G.mapMod R ⋙ comap f).Linear K :=
  functor_linear_of_map_smulEnd _ φ ψ fun a M ↦ by
    have h' : Γ.mapMonoidHom f (ψ a) = Γ.mapFunctorMonoidHom G (φ a) := Γ.ext (h a)
    simp only [Functor.comp_obj, Functor.comp_map]
    rw [smulHom_comap_obj, h', smulHom_mapMod_obj]
    rfl

/-- The image of module objects under an additive lax monoidal functor `G` is `K`-linear, `K`
acting on `G R` through `Γ R →+* Γ (G R)`, provided `G R` is commutative. -/
lemma linear_mapMod [G.Additive] [IsCommMonObj (G.obj R)] (φ : K →+* Γ R) :
    letI := linearOfRingHom φ
    letI := linearOfRingHom ((Γ.mapFunctor G).comp φ)
    (G.mapMod R).Linear K :=
  functor_linear_of_map_smulEnd _ φ _ fun a M ↦ (smulHom_mapMod_obj G (φ a) M).symm

end MapMod

end Comm

end CategoryTheory.Mod

namespace CategoryTheory.Adjunction

open Functor.LaxMonoidal

variable {B : Type*} [Category* B] [MonoidalCategory B] {C : Type u₁} [Category.{v₁} C]
  [MonoidalCategory C] {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Monoidal] [G.LaxMonoidal] [adj.IsMonoidal]
  (P : B ⥤ C) (Q : B ⥤ D) [P.LaxMonoidal] [Q.LaxMonoidal] (τ : P ⋙ F ⟶ Q)
  [NatTrans.IsMonoidal τ]

/-- Images of global sections under the mate of a monoidal natural transformation: for a
monoidal adjunction `F ⊣ G` and a monoidal natural transformation `τ : P ⋙ F ⟶ Q`, the mate
`P ⟶ Q ⋙ G` of `τ` sends the global section `ε ≫ P s` of `P Λ` to the global section
`ε ≫ G (ε ≫ Q s)` of `G (Q Λ)`, for every `s : 𝟙 ⟶ Λ`. -/
@[reassoc]
lemma ε_comp_map_comp_unit_app_comp_map {Λ : B} (s : 𝟙_ B ⟶ Λ) :
    ε P ≫ P.map s ≫ adj.unit.app (P.obj Λ) ≫ G.map (τ.app Λ) = ε G ≫ G.map (ε Q ≫ Q.map s) := by
  have hu : adj.unit.app (𝟙_ C) = ε G ≫ G.map (ε F) := by
    rw [← adj.unit_app_unit_comp_map_η, Category.assoc, ← G.map_comp,
      Functor.Monoidal.η_ε, G.map_id]
    exact (Category.comp_id _).symm
  have hτ := NatTrans.IsMonoidal.unit (τ := τ)
  rw [Functor.LaxMonoidal.comp_ε] at hτ
  rw [← adj.unit_naturality_assoc, ← G.map_comp, ← Functor.comp_map, τ.naturality,
    ← adj.unit_naturality_assoc, hu, Category.assoc, ← G.map_comp, ← G.map_comp, ← hτ]
  simp only [Category.assoc]

end CategoryTheory.Adjunction
