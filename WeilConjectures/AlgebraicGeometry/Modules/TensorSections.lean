/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-!
# Sections of tensor products of modules on a scheme

The tensor product `M ⊗ N` of two `𝒪_X`-modules is the sheafification of the presheaf
`U ↦ Γ(M, U) ⊗_{Γ(X, U)} Γ(N, U)` (`SheafOfModules.tensorObjIsoSheafification`). The forgetful
functor from `𝒪_X`-modules to presheaves of modules is right adjoint to the monoidal
sheafification functor, hence lax monoidal (`Adjunction.rightAdjointLaxMonoidal`); its
tensorator `Γ(M, U) ⊗ Γ(N, U) → Γ(M ⊗ N, U)` sends `x ⊗ y` to the section `tmul x y`.
The coherence axioms of a lax monoidal functor then compute the action of the structural
morphisms of the monoidal category `X.Modules` on such sections.

If `e` is a free generator of `N` on `V`, then on every `W ≤ V` the presheaf tensor product is
already isomorphic to `M` via `x ↦ x ⊗ e|_W`; as the tensorator is locally bijective, this
shows that `x ↦ tmul x e|_W` is a bijection `Γ(M, W) ≃ Γ(M ⊗ N, W)`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.tmul`: the section `x ⊗ y` of `M ⊗ N` over `U`, for
  sections `x` of `M` and `y` of `N` over `U`.
- `AlgebraicGeometry.Scheme.Modules.unitSectionsEquiv`: the sections of the unit
  `𝟙_ X.Modules` over `U` are `Γ(X, U)`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.tensorHom_app_tmul`,
  `AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tmul`,
  `AlgebraicGeometry.Scheme.Modules.associator_hom_app_tmul`,
  `AlgebraicGeometry.Scheme.Modules.braiding_hom_app_tmul`: the structural morphisms of the
  monoidal category `X.Modules` on elementary tensors.
- `AlgebraicGeometry.Scheme.Modules.IsFreeGenerator.bijective_tmul_right`: tensoring with a
  free generator is bijective on sections.
- `AlgebraicGeometry.Scheme.Modules.isFreeGenerator_tmul`: the tensor product of free
  generators is a free generator.
-/

@[expose] public section

universe u

open CategoryTheory Opposite MonoidalCategory TensorProduct

open scoped AlgebraicGeometry.Scheme.Modules

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  [BraidedCategory C] [BraidedCategory D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Braided]

/-- The right adjoint of a braided monoidal functor, with its lax monoidal structure
`Adjunction.rightAdjointLaxMonoidal`, is compatible with the braidings. -/
lemma rightAdjointLaxMonoidal_μ_comp_map_braiding (X Y : D) :
    letI := adj.rightAdjointLaxMonoidal
    Functor.LaxMonoidal.μ G X Y ≫ G.map (β_ X Y).hom =
      (β_ (G.obj X) (G.obj Y)).hom ≫ Functor.LaxMonoidal.μ G Y X := by
  let := adj.rightAdjointLaxMonoidal
  rw [rightAdjointLaxMonoidal_μ, rightAdjointLaxMonoidal_μ, homEquiv_unit, homEquiv_unit,
    Category.assoc, ← G.map_comp, ← adj.unit_naturality_assoc, ← G.map_comp]
  congr 2
  simp

end CategoryTheory.Adjunction

/-- If `e` is a basis of a free module `B` of rank one, i.e. `r ↦ r • e` is bijective, then
`a ↦ a ⊗ₜ e` is a bijection `A → A ⊗[R] B`. -/
lemma TensorProduct.bijective_tmul_right_of_bijective_smul {R A B : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] {e : B}
    (he : Function.Bijective fun r : R ↦ r • e) :
    Function.Bijective fun a : A ↦ a ⊗ₜ[R] e := by
  have he' : Function.Bijective (LinearMap.toSpanSingleton R B e) := he
  let f : R ≃ₗ[R] B := LinearEquiv.ofBijective (LinearMap.toSpanSingleton R B e) he'
  have : (fun a : A ↦ a ⊗ₜ[R] e) =
      TensorProduct.congr (LinearEquiv.refl R A) f ∘ (TensorProduct.rid R A).symm := by
    ext a
    simp only [f, Function.comp_apply, TensorProduct.rid_symm_apply, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
    rw [LinearEquiv.ofBijective_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rw [this]
  exact (EquivLike.bijective _).comp (EquivLike.bijective _)

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] (R : Sheaf J CommRingCat.{u})
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

attribute [local instance] monoidalCategory symmetricCategory

/-- The sheafification functor from presheaves of modules over `R` to sheaves of modules is
monoidal for `SheafOfModules.monoidalCategory`. This names the instance of
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal`, which instance search does not
find for the structure sheaf of a scheme. -/
@[instance_reducible]
noncomputable def sheafificationMonoidal :
    (PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).Monoidal :=
  inferInstance

/-- The sheafification functor from presheaves of modules over `R` to sheaves of modules is
braided for `SheafOfModules.symmetricCategory`. -/
@[instance_reducible]
noncomputable def sheafificationBraided :
    letI := sheafificationMonoidal R
    (PresheafOfModules.sheafification.{u}
      (𝟙 ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj)).Braided :=
  inferInstance

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (X) in
/-- The monoidal structure on presheaves of modules over the structure sheaf of `X`: the
pointwise tensor product. -/
@[instance_reducible]
noncomputable def presheafMonoidalCategory :
    MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs
    (MonoidalCategory (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

variable (X) in
/-- The symmetric monoidal structure on presheaves of modules over the structure sheaf of
`X`. -/
@[instance_reducible]
noncomputable def presheafSymmetricCategory :
    letI := presheafMonoidalCategory X
    SymmetricCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  inferInstanceAs
    (SymmetricCategory (_root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)))

attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory

variable (X) in
/-- The sheafification functor from presheaves of modules over the structure sheaf of `X` to
`𝒪_X`-modules. -/
noncomputable abbrev sheafification :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  _root_.PresheafOfModules.sheafification.{u} (𝟙 X.ringCatSheaf.obj)

attribute [local instance] SheafOfModules.sheafificationMonoidal
  SheafOfModules.sheafificationBraided

variable (X) in
/-- The monoidal structure on the sheafification functor of `X`. -/
@[instance_reducible]
noncomputable def sheafificationMonoidal : (sheafification X).Monoidal :=
  SheafOfModules.sheafificationMonoidal X.sheaf

variable (X) in
/-- The braided structure on the sheafification functor of `X`. -/
@[instance_reducible]
noncomputable def sheafificationBraided :
    letI := sheafificationMonoidal X
    (sheafification X).Braided :=
  SheafOfModules.sheafificationBraided X.sheaf

attribute [local instance] sheafificationMonoidal sheafificationBraided

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules, in the form which is
right adjoint to `sheafification X`. -/
noncomputable abbrev forgetToPresheafOfModules :
    X.Modules ⥤ _root_.PresheafOfModules.{u} X.ringCatSheaf.obj :=
  SheafOfModules.forget _ ⋙ _root_.PresheafOfModules.restrictScalars (𝟙 _)

variable (X) in
/-- The sheafification adjunction for presheaves of modules over the structure sheaf of `X`. -/
noncomputable abbrev sheafificationAdjunction :
    sheafification X ⊣ forgetToPresheafOfModules X :=
  _root_.PresheafOfModules.sheafificationAdjunction.{u} (𝟙 X.ringCatSheaf.obj)

variable (X) in
/-- The forgetful functor from `𝒪_X`-modules to presheaves of modules is lax monoidal, being
right adjoint to the monoidal sheafification functor. -/
@[instance_reducible]
noncomputable def forgetToPresheafOfModulesLaxMonoidal :
    (forgetToPresheafOfModules X).LaxMonoidal :=
  (sheafificationAdjunction X).rightAdjointLaxMonoidal

attribute [local instance] forgetToPresheafOfModulesLaxMonoidal

variable {M N P M' N' : X.Modules} {U : X.Opens}

section Sections

/-- The tensorator of the lax monoidal functor `forgetToPresheafOfModules X` at `M` and `N`. -/
local notation "μ[" M ", " N "]" => Functor.LaxMonoidal.μ (forgetToPresheafOfModules _) M N

variable (M N U) in
/-- The `Γ(X, U)`-linear map `Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) → Γ(M ⊗ N, U)`, the component at `U`
of the canonical map from the presheaf tensor product to its sheafification `M ⊗ N`. -/
noncomputable def tensorSectionsMap :
    Γ(M, U) ⊗[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(M ⊗ N, U) :=
  (μ[M, N].app (op U)).hom

/-- The section `x ⊗ y` of `M ⊗ N` over `U`, for sections `x` of `M` and `y` of `N` over `U`:
the image of the elementary tensor `x ⊗ₜ y` of the presheaf tensor product in its
sheafification `M ⊗ N`. -/
noncomputable def tmul (x : Γ(M, U)) (y : Γ(N, U)) : Γ(M ⊗ N, U) :=
  tensorSectionsMap M N U (x ⊗ₜ y)

lemma tmul_def (x : Γ(M, U)) (y : Γ(N, U)) : tmul x y = tensorSectionsMap M N U (x ⊗ₜ y) :=
  rfl

lemma add_tmul (x x' : Γ(M, U)) (y : Γ(N, U)) : tmul (x + x') y = tmul x y + tmul x' y := by
  rw [tmul_def, tmul_def, tmul_def, TensorProduct.add_tmul, map_add]

lemma tmul_add (x : Γ(M, U)) (y y' : Γ(N, U)) : tmul x (y + y') = tmul x y + tmul x y' := by
  rw [tmul_def, tmul_def, tmul_def, TensorProduct.tmul_add, map_add]

@[simp]
lemma zero_tmul (y : Γ(N, U)) : tmul (0 : Γ(M, U)) y = 0 := by
  rw [tmul_def, TensorProduct.zero_tmul, map_zero]

@[simp]
lemma tmul_zero (x : Γ(M, U)) : tmul x (0 : Γ(N, U)) = 0 := by
  rw [tmul_def, TensorProduct.tmul_zero, map_zero]

lemma smul_tmul (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) : tmul (r • x) y = r • tmul x y := by
  rw [tmul_def, tmul_def, ← TensorProduct.smul_tmul', LinearMap.map_smul]

lemma tmul_smul (r : Γ(X, U)) (x : Γ(M, U)) (y : Γ(N, U)) : tmul x (r • y) = r • tmul x y := by
  rw [tmul_def, tmul_def, TensorProduct.tmul_smul, LinearMap.map_smul]

/-- Restriction of an elementary tensor of sections. -/
lemma presheaf_map_tmul {V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) (y : Γ(N, U)) :
    (M ⊗ N).presheaf.map i.op (tmul x y) =
      tmul (M.presheaf.map i.op x) (N.presheaf.map i.op y) :=
  (_root_.PresheafOfModules.naturality_apply μ[M, N] i.op (x ⊗ₜ y)).symm

/-- Naturality of elementary tensors of sections. -/
lemma tensorHom_app_tmul (f : M ⟶ M') (g : N ⟶ N') (x : Γ(M, U)) (y : Γ(N, U)) :
    (f ⊗ₘ g).app U (tmul x y) = tmul (f.app U x) (g.app U y) :=
  (congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ y))
    (Functor.LaxMonoidal.μ_natural (forgetToPresheafOfModules X) f g)).symm

lemma whiskerLeft_app_tmul (g : N ⟶ N') (x : Γ(M, U)) (y : Γ(N, U)) :
    (M ◁ g).app U (tmul x y) = tmul x (g.app U y) :=
  (congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ y))
    (Functor.LaxMonoidal.μ_natural_right (forgetToPresheafOfModules X) M g)).symm

lemma whiskerRight_app_tmul (f : M ⟶ M') (x : Γ(M, U)) (y : Γ(N, U)) :
    (f ▷ N).app U (tmul x y) = tmul (f.app U x) y :=
  (congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ y))
    (Functor.LaxMonoidal.μ_natural_left (forgetToPresheafOfModules X) f N)).symm

variable (U) in
/-- The sections of the unit `𝟙_ X.Modules = 𝒪_X` over `U` are the functions `Γ(X, U)`. -/
noncomputable def unitSectionsEquiv : Γ(X, U) ≃ₗ[Γ(X, U)] Γ(𝟙_ X.Modules, U) :=
  LinearEquiv.refl _ _

/-- A section of the unit is a multiple of the section `1`. -/
lemma unitSectionsEquiv_eq_smul_one (r : Γ(X, U)) :
    unitSectionsEquiv U r = r • unitSectionsEquiv U 1 := by
  rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]

/-- Restriction of sections of the unit is restriction of functions. -/
lemma presheaf_map_unitSectionsEquiv {V : X.Opens} (i : V ⟶ U) (r : Γ(X, U)) :
    (𝟙_ X.Modules).presheaf.map i.op (unitSectionsEquiv U r) =
      unitSectionsEquiv V (X.presheaf.map i.op r) :=
  rfl

/-- The unit of the lax monoidal functor `forgetToPresheafOfModules X` is the identity. -/
lemma ε_forgetToPresheafOfModules_app (r : Γ(X, U)) :
    (Functor.LaxMonoidal.ε (forgetToPresheafOfModules X)).app (op U) r =
      unitSectionsEquiv U r :=
  congr_arg (fun φ ↦ φ.app (op U) r)
    ((sheafificationAdjunction X).right_triangle_components (SheafOfModules.unit _))

/-- The left unitor on elementary tensors: `1 ⊗ x ↦ x`. -/
lemma leftUnitor_hom_app_tmul (r : Γ(X, U)) (x : Γ(M, U)) :
    (λ_ M).hom.app U (tmul (unitSectionsEquiv U r) x) = r • x := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op U) (r ⊗ₜ x))
    (Functor.LaxMonoidal.left_unitality (forgetToPresheafOfModules X) M)).symm

/-- The right unitor on elementary tensors: `x ⊗ 1 ↦ x`. -/
lemma rightUnitor_hom_app_tmul (r : Γ(X, U)) (x : Γ(M, U)) :
    (ρ_ M).hom.app U (tmul x (unitSectionsEquiv U r)) = r • x := by
  rw [← ε_forgetToPresheafOfModules_app]
  exact (congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ r))
    (Functor.LaxMonoidal.right_unitality (forgetToPresheafOfModules X) M)).symm

/-- The left unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma leftUnitor_hom_app_tmul' (s : Γ(𝟙_ X.Modules, U)) (x : Γ(M, U)) :
    (λ_ M).hom.app U (tmul s x) = (unitSectionsEquiv U).symm s • x := by
  rw [← leftUnitor_hom_app_tmul, LinearEquiv.apply_symm_apply]

/-- The right unitor on elementary tensors, for an arbitrary section of the unit. -/
lemma rightUnitor_hom_app_tmul' (x : Γ(M, U)) (s : Γ(𝟙_ X.Modules, U)) :
    (ρ_ M).hom.app U (tmul x s) = (unitSectionsEquiv U).symm s • x := by
  rw [← rightUnitor_hom_app_tmul, LinearEquiv.apply_symm_apply]

/-- The associator on elementary tensors: `(x ⊗ y) ⊗ z ↦ x ⊗ (y ⊗ z)`. -/
lemma associator_hom_app_tmul (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (α_ M N P).hom.app U (tmul (tmul x y) z) = tmul x (tmul y z) :=
  congr_arg (fun φ ↦ φ.app (op U) ((x ⊗ₜ y) ⊗ₜ z))
    (Functor.LaxMonoidal.associativity (forgetToPresheafOfModules X) M N P)

/-- The braiding on elementary tensors: `x ⊗ y ↦ y ⊗ x`. -/
lemma braiding_hom_app_tmul (x : Γ(M, U)) (y : Γ(N, U)) :
    (β_ M N).hom.app U (tmul x y) = tmul y x :=
  congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ y))
    ((sheafificationAdjunction X).rightAdjointLaxMonoidal_μ_comp_map_braiding M N)

/-- The inverse of an isomorphism of modules undoes it on sections. -/
lemma Iso.inv_app_hom_app_apply (e : M ≅ N) (z : Γ(M, U)) : e.inv.app U (e.hom.app U z) = z := by
  rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
  rfl

/-- An isomorphism of modules is bijective on sections. -/
lemma Iso.bijective_hom_app (e : M ≅ N) (U : X.Opens) : Function.Bijective (e.hom.app U) :=
  ConcreteCategory.bijective_of_isIso (e.hom.app U)

/-- The inverse of the left unitor: `x ↦ 1 ⊗ x`. -/
lemma leftUnitor_inv_app (x : Γ(M, U)) :
    (λ_ M).inv.app U x = tmul (unitSectionsEquiv U 1) x := by
  conv_lhs => rw [← one_smul Γ(X, U) x, ← leftUnitor_hom_app_tmul]
  exact Iso.inv_app_hom_app_apply _ _

/-- The inverse of the right unitor: `x ↦ x ⊗ 1`. -/
lemma rightUnitor_inv_app (x : Γ(M, U)) :
    (ρ_ M).inv.app U x = tmul x (unitSectionsEquiv U 1) := by
  conv_lhs => rw [← one_smul Γ(X, U) x, ← rightUnitor_hom_app_tmul]
  exact Iso.inv_app_hom_app_apply _ _

/-- The inverse of the associator: `x ⊗ (y ⊗ z) ↦ (x ⊗ y) ⊗ z`. -/
lemma associator_inv_app_tmul (x : Γ(M, U)) (y : Γ(N, U)) (z : Γ(P, U)) :
    (α_ M N P).inv.app U (tmul x (tmul y z)) = tmul (tmul x y) z := by
  rw [← associator_hom_app_tmul]
  exact Iso.inv_app_hom_app_apply _ _

variable (M N) in
/-- The map from the presheaf tensor product to `M ⊗ N` is the unit of the sheafification
adjunction followed by an isomorphism. -/
lemma toPresheaf_map_μ :
    (_root_.PresheafOfModules.toPresheaf _).map μ[M, N] =
      CategoryTheory.toSheafify _ _ ≫ (_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules X).map (Functor.OplaxMonoidal.δ (sheafification X) _ _ ≫
          ((sheafificationAdjunction X).counit.app M ⊗ₘ
            (sheafificationAdjunction X).counit.app N))) := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit, Functor.map_comp]
  exact congr_arg (· ≫ _)
    (_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app _ _)

variable (M N) in
/-- The comparison isomorphism `a(M ⊗ₚ N) ≅ M ⊗ N`, seen on underlying presheaves. -/
instance isIso_toPresheaf_map_δ_comp_counit :
    IsIso ((_root_.PresheafOfModules.toPresheaf _).map
        ((forgetToPresheafOfModules X).map (Functor.OplaxMonoidal.δ (sheafification X) _ _ ≫
          ((sheafificationAdjunction X).counit.app M ⊗ₘ
            (sheafificationAdjunction X).counit.app N)))) := by
  have : IsIso (sheafificationAdjunction X).counit :=
    (inferInstance : IsIso (_root_.PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 X.ringCatSheaf.obj)).counit)
  infer_instance

variable (M N) in
/-- The map from the presheaf tensor product to `M ⊗ N` becomes an isomorphism after
sheafification. -/
lemma W_toPresheaf_map_μ :
    (Opens.grothendieckTopology X).W ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) := by
  rw [toPresheaf_map_μ]
  exact MorphismProperty.comp_mem _ _ _ ((Opens.grothendieckTopology X).W_toSheafify _)
    (MorphismProperty.of_isIso _ _)

instance : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) :=
  (W_toPresheaf_map_μ M N).isLocallyInjective

instance : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) :=
  (W_toPresheaf_map_μ M N).isLocallySurjective

/-- Tensoring with a free generator `e` of `N` on `V` is injective on sections over `W ≤ V`. -/
lemma IsFreeGenerator.injective_tmul_right {V : X.Opens} {e : Γ(N, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Injective fun x : Γ(M, W) ↦ tmul x (N.presheaf.map (homOfLE h).op e) := by
  intro x x' hxx'
  have hS := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) (X := op W)
    (x ⊗ₜ[Γ(X, W)] N.presheaf.map (homOfLE h).op e : Γ(M, W) ⊗[Γ(X, W)] Γ(N, W))
    (x' ⊗ₜ[Γ(X, W)] N.presheaf.map (homOfLE h).op e : Γ(M, W) ⊗[Γ(X, W)] Γ(N, W)) hxx'
  refine (M.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W' f hf ↦ ?_
  apply (TensorProduct.bijective_tmul_right_of_bijective_smul (A := Γ(M, W'))
    (he.map ((leOfHom f).trans h)).bijective).1
  have hf' : M.presheaf.map f.op x ⊗ₜ[Γ(X, W')]
        N.presheaf.map f.op (N.presheaf.map (homOfLE h).op e) =
      M.presheaf.map f.op x' ⊗ₜ[Γ(X, W')]
        N.presheaf.map f.op (N.presheaf.map (homOfLE h).op e) := hf
  rw [presheaf_map_map_apply] at hf'
  exact hf'

/-- Restriction of an elementary tensor with a restriction of a fixed section `e`. -/
lemma presheaf_map_tmul_presheaf_map {V W W' : X.Opens} (e : Γ(N, V)) (h : W ≤ V)
    (h' : W' ≤ V) (g : W' ⟶ W) (x : Γ(M, W)) :
    (M ⊗ N).presheaf.map g.op (tmul x (N.presheaf.map (homOfLE h).op e)) =
      tmul (M.presheaf.map g.op x) (N.presheaf.map (homOfLE h').op e) := by
  rw [presheaf_map_tmul, presheaf_map_map_apply]
  rfl

/-- **Local triviality of tensor products.** If `e` is a free generator of `N` on `V`, then
`x ↦ x ⊗ e|_W` is a bijection `Γ(M, W) → Γ(M ⊗ N, W)` for every `W ≤ V`.

The map from the presheaf tensor product to `M ⊗ N` is locally bijective, and on opens
contained in `V` the presheaf tensor product is identified with `M` by `x ↦ x ⊗ e`; one
concludes with the sheaf property of `M` and `M ⊗ N`. -/
lemma IsFreeGenerator.bijective_tmul_right {V : X.Opens} {e : Γ(N, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Bijective fun x : Γ(M, W) ↦ tmul x (N.presheaf.map (homOfLE h).op e) := by
  refine ⟨he.injective_tmul_right h, fun s ↦ ?_⟩
  have hS := Presheaf.imageSieve_mem (Opens.grothendieckTopology X)
    ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) (U := op W) s
  have hb (W' : X.Opens) (f : W' ⟶ W) := (TensorProduct.bijective_tmul_right_of_bijective_smul
    (A := Γ(M, W')) (he.map ((leOfHom f).trans h)).bijective).2
  let x : Presieve.FamilyOfElements (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat)
      (Presheaf.imageSieve ((_root_.PresheafOfModules.toPresheaf _).map μ[M, N]) s).arrows :=
    fun W' f hf ↦ Function.surjInv (hb W' f)
      (Presheaf.localPreimage _ s f hf : Γ(M, W') ⊗[Γ(X, W')] Γ(N, W'))
  have hx {W' : X.Opens} (f : W' ⟶ W) (hf) :
      tmul (x f hf) (N.presheaf.map (homOfLE ((leOfHom f).trans h)).op e) =
        (M ⊗ N).presheaf.map f.op s :=
    (congr_arg (tensorSectionsMap M N W') (Function.surjInv_eq (hb W' f) _)).trans
      (Presheaf.app_localPreimage _ s f hf)
  have hcompat : x.Compatible := by
    intro Z₁ Z₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomm
    have hZ : Z ≤ V := (leOfHom (g₁ ≫ f₁)).trans h
    have e₁ := presheaf_map_tmul_presheaf_map e ((leOfHom f₁).trans h) hZ g₁ (x f₁ hf₁)
    have e₂ := presheaf_map_tmul_presheaf_map e ((leOfHom f₂).trans h) hZ g₂ (x f₂ hf₂)
    rw [hx, presheaf_map_map_apply, hcomm] at e₁
    rw [hx, presheaf_map_map_apply] at e₂
    exact he.injective_tmul_right hZ (e₁.symm.trans e₂)
  have hM := M.isSheaf_presheaf_comp_forget _ hS
  refine ⟨hM.amalgamate x hcompat,
    ((M ⊗ N).isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun W' f hf ↦ ?_⟩
  exact (presheaf_map_tmul_presheaf_map e h ((leOfHom f).trans h) f _).trans
    ((congrArg (tmul · _) (hM.valid_glue hcompat f hf)).trans (hx f hf))

/-- **Local triviality of tensor products**, with the free generator on the left: if `e` is a
free generator of `M` on `V`, then `y ↦ e|_W ⊗ y` is a bijection `Γ(N, W) → Γ(M ⊗ N, W)` for
every `W ≤ V`. -/
lemma IsFreeGenerator.bijective_tmul_left {V : X.Opens} {e : Γ(M, V)}
    (he : IsFreeGenerator e) {W : X.Opens} (h : W ≤ V) :
    Function.Bijective fun y : Γ(N, W) ↦ tmul (M.presheaf.map (homOfLE h).op e) y := by
  have : (fun y : Γ(N, W) ↦ tmul (M.presheaf.map (homOfLE h).op e) y) =
      (β_ N M).hom.app W ∘ fun y : Γ(N, W) ↦ tmul y (M.presheaf.map (homOfLE h).op e) := by
    ext y
    exact (braiding_hom_app_tmul _ _).symm
  rw [this]
  exact (Iso.bijective_hom_app _ W).comp (he.bijective_tmul_right h)

/-- The tensor product of free generators is a free generator of the tensor product. -/
lemma isFreeGenerator_tmul {V : X.Opens} {e : Γ(M, V)} {e' : Γ(N, V)}
    (he : IsFreeGenerator e) (he' : IsFreeGenerator e') : IsFreeGenerator (tmul e e') := by
  intro W h
  have : (fun r : Γ(X, W) ↦ r • (M ⊗ N).presheaf.map (homOfLE h).op (tmul e e')) =
      (fun x : Γ(M, W) ↦ tmul x (N.presheaf.map (homOfLE h).op e')) ∘
        fun r : Γ(X, W) ↦ r • M.presheaf.map (homOfLE h).op e := by
    ext r
    simp only [Function.comp_apply, presheaf_map_tmul, smul_tmul]
  rw [this]
  exact (he'.bijective_tmul_right h).comp (he W h)

end Sections

end AlgebraicGeometry.Scheme.Modules
