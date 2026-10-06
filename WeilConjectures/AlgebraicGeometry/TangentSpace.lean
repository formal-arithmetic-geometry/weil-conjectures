/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict

/-!
# Cotangent and tangent sheaves of a morphism of schemes

For a morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials `Ω¹_{X/S}` is the
sheafification of the presheaf `U ↦ Ω_{𝒪_X(U) / (f⁻¹𝒪_S)(U)}` of Kähler differentials of `𝒪_X`
relative to the pullback `f⁻¹𝒪_S` of the structure sheaf of the base. It comes with the universal
relative derivation `d : 𝒪_X → Ω¹_{X/S}`. The *tangent sheaf* is its dual

$$
T_{X/S} = \mathcal{H}om_{\mathcal O_X}(\Omega^1_{X/S}, \mathcal O_X),
$$

the sheaf of relative vector fields, that is of derivations of `𝒪_X` over `f⁻¹𝒪_S`. For a section
`e : S ⟶ X` of `f`, the *tangent sheaf along `e`* is

$$
\mathcal{H}om_{\mathcal O_S}(e^*\Omega^1_{X/S}, \mathcal O_S),
$$

the sheaf of relative tangent vectors at the points of the section. When `f` is smooth, `Ω¹_{X/S}`
is locally free and this is `e^* T_{X/S}`. For the identity section of a group scheme this is the
Lie algebra sheaf, see `WeilConjectures.AlgebraicGeometry.GroupScheme.Lie`.

Mathlib has sheaves of modules on schemes with their pullbacks and pushforwards, and Kähler
differentials of a morphism of presheaves of commutative rings on one site, but neither the
cotangent sheaf of a morphism of schemes nor the sheaf `ℋom(M, 𝒪_X)`. Both are constructed here.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.dual`: the sheaf `ℋom_{𝒪_X}(M, 𝒪_X)` of an `𝒪_X`-module `M`,
  with sections over `U` the morphisms `M|_U ⟶ 𝒪_U`.
- `AlgebraicGeometry.Scheme.Hom.cotangentPresheaf`, `AlgebraicGeometry.Scheme.Hom.cotangentSheaf`:
  the presheaf and the sheaf `Ω¹_{X/S}` of relative differentials of `f : X ⟶ S`.
- `AlgebraicGeometry.Scheme.Hom.tangentSheaf`: the tangent sheaf `T_{X/S} = ℋom(Ω¹_{X/S}, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong`: the tangent sheaf `ℋom(e^*Ω¹_{X/S}, 𝒪_S)`
  along a section `e : S ⟶ X`.

## Main results

- `AlgebraicGeometry.Scheme.Modules.dualPresheafAbCompForgetIso`: the sections of the dual over
  `U` are the `𝒪_X`-linear morphisms between the restrictions of `M` and `𝒪_X` to the opens
  `W ≤ U` of `X`. This is what makes the dual a sheaf.
- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong_iso_pullback_tangentSheaf`: for smooth `f`,
  the tangent sheaf along a section is the pullback of the tangent sheaf.

## Blueprint

- `sk-d-tangent`: the tangent space of a point as the dual of the cotangent space `𝔪_x/𝔪_x²`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme

/-! ### The dual of a sheaf of modules -/

namespace Modules

variable (X : Scheme.{u})

/-- The structure sheaf `𝒪_X` as a sheaf of `𝒪_X`-modules. -/
noncomputable abbrev unitModule : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X}

/-- Multiplication by a global section `r` of `𝒪_X`, as an endomorphism of the sheaf of modules
`𝒪_X`. -/
noncomputable def unitSmul (r : Γ(X, ⊤)) : unitModule X ⟶ unitModule X :=
  (SheafOfModules.unitHomEquiv _).symm
    (PresheafOfModules.sectionsMk (fun U ↦ X.presheaf.map (homOfLE le_top : U.unop ⟶ ⊤).op r)
      (fun U V f ↦ by
        change X.presheaf.map f (X.presheaf.map _ r) = X.presheaf.map _ r
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl))

@[simp]
theorem unitSmul_app (r : Γ(X, ⊤)) (U : X.Opens) (x : Γ(X, U)) :
    ((unitSmul r).app U).hom x = x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r :=
  rfl

theorem unitSmul_one : unitSmul (1 : Γ(X, ⊤)) = 𝟙 _ := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app]
  rw [map_one, mul_one]
  rfl

theorem unitSmul_mul (r s : Γ(X, ⊤)) : unitSmul (r * s) = unitSmul s ≫ unitSmul r := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app, unitSmul_app, unitSmul_app]
  rw [map_mul, mul_assoc, mul_comm (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r)]

theorem unitSmul_add (r s : Γ(X, ⊤)) : unitSmul (r + s) = unitSmul r + unitSmul s := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  change _ = ((unitSmul r).app U).hom x + ((unitSmul s).app U).hom x
  erw [unitSmul_app, unitSmul_app, unitSmul_app]
  change x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (r + s) =
    x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op r +
      x * X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op s
  rw [map_add, mul_add]

theorem unitSmul_zero : unitSmul (0 : Γ(X, ⊤)) = 0 := by
  ext U x
  revert x
  intro (x : Γ(X, U))
  erw [unitSmul_app]
  rw [map_zero, mul_zero]
  rfl

/-- The `Γ(X, ⊤)`-module structure on the morphisms `M ⟶ 𝒪_X` of sheaves of modules: `r • φ` is
`φ` followed by multiplication by `r`. These are the global sections of the dual sheaf. -/
noncomputable instance instModuleHomUnit (M : X.Modules) : Module Γ(X, ⊤) (M ⟶ unitModule X) where
  smul r φ := φ ≫ unitSmul r
  one_smul φ := by
    change φ ≫ unitSmul 1 = φ
    rw [unitSmul_one, Category.comp_id]
  mul_smul r s φ := by
    change φ ≫ unitSmul (r * s) = (φ ≫ unitSmul s) ≫ unitSmul r
    simp only [unitSmul_mul, Category.assoc]
  smul_zero r := by
    change (0 : M ⟶ unitModule X) ≫ unitSmul r = 0
    rw [Limits.zero_comp]
  smul_add r φ ψ := by
    change (φ + ψ) ≫ unitSmul r = φ ≫ _ + ψ ≫ _
    rw [Preadditive.add_comp]
  add_smul r s φ := by
    change φ ≫ unitSmul (r + s) = φ ≫ _ + φ ≫ _
    rw [unitSmul_add, Preadditive.comp_add]
  zero_smul φ := by
    change φ ≫ unitSmul 0 = 0
    rw [unitSmul_zero, Limits.comp_zero]

theorem homUnit_smul_def {M : X.Modules} (r : Γ(X, ⊤)) (φ : M ⟶ unitModule X) :
    r • φ = φ ≫ unitSmul r :=
  rfl

variable (M : X.Modules)

/-- The sections over `U` of the dual sheaf `ℋom_{𝒪_X}(M, 𝒪_X)`: the morphisms `M|_U ⟶ 𝒪_U` of
sheaves of modules on `U`. -/
abbrev DualSections (U : X.Opens) : Type u :=
  M.restrict U.ι ⟶ unitModule (↑U : Scheme.{u})

noncomputable instance (U : X.Opens) : AddCommGroup (M.DualSections U) :=
  Preadditive.homGroup _ _

/-- The `Γ(X, U)`-module structure on the sections of the dual sheaf over `U`: `r • φ` is `φ`
followed by multiplication by `r`. -/
noncomputable instance (U : X.Opens) : Module Γ(X, U) (M.DualSections U) where
  smul r φ := φ ≫ unitSmul (U.topIso.inv r)
  one_smul φ := by
    change φ ≫ unitSmul (U.topIso.inv 1) = φ
    rw [map_one, unitSmul_one, Category.comp_id]
  mul_smul r s φ := by
    change φ ≫ unitSmul (U.topIso.inv (r * s)) =
      (φ ≫ unitSmul (U.topIso.inv s)) ≫ unitSmul (U.topIso.inv r)
    simp only [map_mul, unitSmul_mul, Category.assoc]
  smul_zero r := by
    change (0 : M.DualSections U) ≫ unitSmul (U.topIso.inv r) = 0
    rw [Limits.zero_comp]
  smul_add r φ ψ := by
    change (φ + ψ) ≫ unitSmul (U.topIso.inv r) = φ ≫ _ + ψ ≫ _
    rw [Preadditive.add_comp]
  add_smul r s φ := by
    change φ ≫ unitSmul (U.topIso.inv (r + s)) = φ ≫ _ + φ ≫ _
    rw [map_add, unitSmul_add, Preadditive.comp_add]
  zero_smul φ := by
    change φ ≫ unitSmul (U.topIso.inv 0) = 0
    rw [map_zero, unitSmul_zero, Limits.comp_zero]

theorem smul_def {U : X.Opens} (r : Γ(X, U)) (φ : M.DualSections U) :
    r • φ = φ ≫ unitSmul (U.topIso.inv r) :=
  rfl

theorem restrictFunctor_map_add {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f] {M N : Z.Modules}
    (φ ψ : M ⟶ N) :
    (restrictFunctor f).map (φ + ψ) = (restrictFunctor f).map φ + (restrictFunctor f).map ψ :=
  rfl

theorem restrictFunctor_map_zero {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    {M N : Z.Modules} : (restrictFunctor f).map (0 : M ⟶ N) = 0 :=
  rfl

/-- Restriction of a section of the dual sheaf from `U` to `V ≤ U`: restrict `φ : M|_U ⟶ 𝒪_U`
along the open immersion `V ⟶ U`. -/
noncomputable def dualRestrict {U V : X.Opens} (h : V ≤ U) (φ : M.DualSections U) :
    M.DualSections V :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).hom.app M ≫
    (restrictFunctorComp (X.homOfLE h) U.ι).hom.app M ≫
      (restrictFunctor (X.homOfLE h)).map φ ≫ (restrictUnitIso (X.homOfLE h)).hom

/-- The component at `P` of `restrictUnitIso f`. -/
noncomputable def restrictUnitHomApp {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : X.Opens) : Γ((unitModule Y).restrict f, P) ⟶ Γ(unitModule X, P) :=
  (restrictUnitIso f).hom.app P

/-- The component at `P` of the inverse of `restrictUnitIso f`. -/
noncomputable def restrictUnitInvApp {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (P : X.Opens) : Γ(unitModule X, P) ⟶ Γ((unitModule Y).restrict f, P) :=
  (restrictUnitIso f).inv.app P

instance {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (P : X.Opens) :
    IsIso (restrictUnitInvApp f P) :=
  Hom.isIso_iff_isIso_app.mp (Iso.isIso_inv (restrictUnitIso f)) P

@[reassoc (attr := simp)]
lemma restrictUnitHomApp_inv {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (P : X.Opens) :
    restrictUnitHomApp f P ≫ restrictUnitInvApp f P = 𝟙 _ := by
  exact congr_arg (fun φ ↦ Hom.app φ P) (restrictUnitIso f).hom_inv_id

lemma restrictUnitInvApp_smul {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (P : X.Opens)
    (s : Γ(X, P)) (z : Γ(unitModule X, P)) :
    restrictUnitInvApp f P (s • z) = s • restrictUnitInvApp f P z :=
  Hom.app_smul (M := unitModule X) (N := (unitModule Y).restrict f) _ _ _

@[reassoc]
lemma restrictUnitHomApp_naturality {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {P Q : X.Opens} (i : P ⟶ Q) :
    ((unitModule Y).restrict f).presheaf.map i.op ≫ restrictUnitHomApp f P =
      restrictUnitHomApp f Q ≫ (unitModule X).presheaf.map i.op :=
  Modules.Hom.naturality (M := (unitModule Y).restrict f) (N := unitModule X)
    (restrictUnitIso f).hom i

@[reassoc]
lemma restrictUnitInvApp_naturality {Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {P Q : X.Opens} (i : P ⟶ Q) :
    (unitModule X).presheaf.map i.op ≫ restrictUnitInvApp f P =
      restrictUnitInvApp f Q ≫ ((unitModule Y).restrict f).presheaf.map i.op :=
  Modules.Hom.naturality (M := unitModule X) (N := (unitModule Y).restrict f)
    (restrictUnitIso f).inv i

/-- The component over an open `W ≤ U` of `X` of a section of the dual over `U`. -/
noncomputable def dualApp {U : X.Opens} (φ : M.DualSections U) {W : X.Opens} (h : W ≤ U) :
    Γ(M, W) ⟶ Γ(unitModule X, W) :=
  M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op ≫ (M.restrictAppIso U.ι _).inv ≫
    φ.app (U.ι ⁻¹ᵁ W) ≫ restrictUnitInvApp U.ι (U.ι ⁻¹ᵁ W) ≫
    ((unitModule X).restrictAppIso U.ι _).hom ≫
    (unitModule X).presheaf.map (homOfLE (Opens.le_ι_image_ι_preimage h)).op

variable {M}

/-- The components of a section of the dual commute with the restriction maps. -/
@[reassoc]
lemma dualApp_naturality {U : X.Opens} (φ : M.DualSections U) {W₁ W₂ : X.Opens} (h₁ : W₁ ≤ U)
    (i : W₂ ⟶ W₁) :
    M.dualApp φ h₁ ≫ (unitModule X).presheaf.map i.op =
      M.presheaf.map i.op ≫ M.dualApp φ ((leOfHom i).trans h₁) := by
  have e₁ := Modules.Hom.naturality φ (U.ι.preimage_mono (leOfHom i)).hom
  have e₂ := restrictUnitInvApp_naturality U.ι (U.ι.preimage_mono (leOfHom i)).hom
  have e₃ : M.presheaf.map i.op ≫ M.presheaf.map (homOfLE (U.ι.image_preimage_le W₂)).op =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le W₁)).op ≫
        M.presheaf.map (homOfLE (U.ι.image_mono (U.ι.preimage_mono (leOfHom i)))).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  simp only [dualApp, Category.assoc]
  rw [reassoc_of% e₃, ← restrictAppIso_inv_map_assoc U.ι M (U.ι.preimage_mono (leOfHom i)).hom.op,
    reassoc_of% e₁, reassoc_of% e₂, map_restrictAppIso_hom_assoc, ← Functor.map_comp,
    ← Functor.map_comp]
  rfl

/-- The sections over `P` of the restriction of a section `φ` of the dual from `U` to `V`,
in terms of `φ`. -/
lemma dualRestrict_app {U V : X.Opens} (h : V ≤ U) (φ : M.DualSections U)
    (P : (V : Scheme.{u}).Opens) :
    (M.dualRestrict h φ).app P = (M.restrictAppIso V.ι P).hom ≫
      M.presheaf.map (homOfLE ((X.ι_image_homOfLE_image h P).le)).op ≫
      (M.restrictAppIso U.ι _).inv ≫ φ.app (X.homOfLE h ''ᵁ P) ≫
      ((unitModule U).restrictAppIso (X.homOfLE h) P).inv ≫ restrictUnitHomApp (X.homOfLE h) P := by
  simp only [dualRestrict, Hom.comp_app, restrictFunctorCongr_hom_app_app,
    restrictFunctorComp_hom_app_app, restrictFunctor_map_app]
  unfold restrictUnitHomApp
  erw [← Functor.map_comp_assoc]
  rfl

/-- Restricting a section of the dual does not change its components. -/
lemma dualApp_dualRestrict {U V : X.Opens} (h : V ≤ U) (φ : M.DualSections U) {W : X.Opens}
    (hW : W ≤ V) : M.dualApp (M.dualRestrict h φ) hW = M.dualApp φ (hW.trans h) := by
  have hk : X.homOfLE h ''ᵁ V.ι ⁻¹ᵁ W ≤ U.ι ⁻¹ᵁ W := by
    rw [← Hom.preimage_image_eq U.ι (X.homOfLE h ''ᵁ V.ι ⁻¹ᵁ W)]
    exact U.ι.preimage_mono (((X.ι_image_homOfLE_image h _).le).trans (V.ι.image_preimage_le W))
  have e₁ := Modules.Hom.naturality φ hk.hom
  have e₂ : M.presheaf.map (homOfLE (V.ι.image_preimage_le W)).op ≫
      M.presheaf.map (homOfLE ((X.ι_image_homOfLE_image h (V.ι ⁻¹ᵁ W)).le)).op =
      M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op ≫
        M.presheaf.map (homOfLE (U.ι.image_mono hk)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  simp only [dualApp, dualRestrict_app, Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% e₂, ← restrictAppIso_inv_map_assoc U.ι M hk.hom.op, reassoc_of% e₁]
  congr 3
  ext y
  change X.presheaf.map (homOfLE _).op ((V.ι.appIso (V.ι ⁻¹ᵁ W)).inv (((X.homOfLE h).appIso
    (V.ι ⁻¹ᵁ W)).hom (X.presheaf.map (homOfLE (U.ι.image_mono hk)).op y))) =
      X.presheaf.map (homOfLE _).op ((U.ι.appIso (U.ι ⁻¹ᵁ W)).inv y)
  rw [Opens.ι_appIso, Opens.ι_appIso, Hom.appIso_homOfLE_hom]
  refine congrArg (fun f : _ ⟶ Γ(X, W) ↦ f y) (?_ : X.presheaf.map _ ≫
    X.presheaf.map _ ≫ (Iso.refl _).inv ≫ X.presheaf.map _ = (Iso.refl _).inv ≫ X.presheaf.map _)
  simp only [Iso.refl_inv, Category.id_comp]
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

/-- The component of a section `φ` of the dual over the image of an open `V` of `U` is `φ`
over `V`. -/
lemma dualApp_ι_image {U : X.Opens} (φ : M.DualSections U) (V : (U : Scheme.{u}).Opens) :
    M.dualApp φ (U.ι_image_le V) = (M.restrictAppIso U.ι V).inv ≫ φ.app V ≫
      restrictUnitInvApp U.ι V ≫ ((unitModule X).restrictAppIso U.ι V).hom := by
  have hk : U.ι ⁻¹ᵁ U.ι ''ᵁ V ≤ V := (Hom.preimage_image_eq U.ι V).le
  have e₁ := Modules.Hom.naturality φ hk.hom
  have e₂ : M.presheaf.map (homOfLE (U.ι.image_preimage_le (U.ι ''ᵁ V))).op =
      M.presheaf.map (homOfLE (U.ι.image_mono hk)).op := rfl
  have e₃ : (unitModule X).presheaf.map (homOfLE (U.ι.image_mono hk)).op ≫
      (unitModule X).presheaf.map (homOfLE (Opens.le_ι_image_ι_preimage (U.ι_image_le V))).op =
      𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp]
    exact (unitModule X).presheaf.map_id _
  simp only [dualApp]
  rw [e₂, ← restrictAppIso_inv_map_assoc U.ι M hk.hom.op, reassoc_of% e₁,
    restrictUnitInvApp_naturality_assoc, map_restrictAppIso_hom_assoc, e₃, Category.comp_id]

/-- A section of the dual is determined by its components. -/
lemma dualApp_ext {U : X.Opens} {φ ψ : M.DualSections U}
    (h : ∀ (W : X.Opens) (hW : W ≤ U), M.dualApp φ hW = M.dualApp ψ hW) : φ = ψ := by
  ext V : 1
  have := h _ (U.ι_image_le V)
  rw [dualApp_ι_image, dualApp_ι_image, cancel_epi, ← Category.assoc, ← Category.assoc,
    cancel_mono, cancel_mono] at this
  exact this

/-- The components of `r • φ` are those of `φ` followed by multiplication by `r`. -/
lemma dualApp_smul {U : X.Opens} (r : Γ(X, U)) (φ : M.DualSections U) {W : X.Opens}
    (hW : W ≤ U) (x : Γ(M, W)) :
    M.dualApp (r • φ) hW x =
      (show Γ(X, W) from M.dualApp φ hW x) * X.presheaf.map (homOfLE hW).op r := by
  simp only [dualApp, smul_def, Hom.comp_app, Category.assoc, CategoryTheory.comp_apply]
  generalize (φ.app (U.ι ⁻¹ᵁ W)) _ = y
  change X.presheaf.map (homOfLE _).op ((U.ι.appIso (U.ι ⁻¹ᵁ W)).inv
      ((show Γ(U, U.ι ⁻¹ᵁ W) from y) * (U : Scheme.{u}).presheaf.map
        (homOfLE le_top : U.ι ⁻¹ᵁ W ⟶ ⊤).op (U.topIso.inv r))) =
    X.presheaf.map (homOfLE _).op ((U.ι.appIso (U.ι ⁻¹ᵁ W)).inv y) *
      X.presheaf.map (homOfLE hW).op r
  rw [map_mul, map_mul]
  congr 1
  rw [Opens.ι_appIso, Opens.topIso_inv]
  refine congrArg (fun f : _ ⟶ Γ(X, W) ↦ f r) (?_ : X.presheaf.map _ ≫
    X.presheaf.map _ ≫ (Iso.refl _).inv ≫ X.presheaf.map _ = X.presheaf.map _)
  simp only [Iso.refl_inv, Category.id_comp]
  erw [← Functor.map_comp, ← Functor.map_comp]
  rfl

variable (M) in
/-- The section of the dual over `U` with prescribed components `α` over the opens `W ≤ U`. -/
noncomputable def dualMk {U : X.Opens}
    (α : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ (unitModule X).presheaf)
    (hα : ∀ (W : (Over U)ᵒᵖ) (r : Γ(X, W.unop.left)) (m : Γ(M, W.unop.left)),
      α.app W (r • m) = r • show Γ(unitModule X, W.unop.left) from α.app W m) :
    M.DualSections U where
  val := PresheafOfModules.homMk
    { app V := (M.restrictAppIso U.ι V.unop).hom ≫
        α.app (op (Over.mk (homOfLE (U.ι_image_le V.unop)))) ≫
        ((unitModule X).restrictAppIso U.ι V.unop).inv ≫ restrictUnitHomApp U.ι V.unop
      naturality V₁ V₂ i := by
        have e := α.naturality (Over.homMk (homOfLE (U.ι.image_mono (leOfHom i.unop))) :
          Over.mk (homOfLE (U.ι_image_le V₂.unop)) ⟶ Over.mk (homOfLE (U.ι_image_le V₁.unop))).op
        change (M.restrict U.ι).presheaf.map i.unop.op ≫ _ =
          _ ≫ (unitModule U).presheaf.map i.unop.op
        have h₁ := map_restrictAppIso_hom U.ι M i.unop.op
        have h₂ := restrictUnitHomApp_naturality U.ι i.unop
        have h₃ := restrictAppIso_inv_map U.ι (unitModule X) i.unop.op
        dsimp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op,
          Over.homMk_left] at e
        refine ((reassoc_of% h₁) _).trans ((_ ≫= (reassoc_of% e) _).trans
          ((_ ≫= _ ≫= ((reassoc_of% h₃) _).symm).trans ((_ ≫= _ ≫= _ ≫= h₂).trans ?_)))
        exact ((Category.assoc _ _ _).trans (_ ≫= ((Category.assoc _ _ _).trans
          (_ ≫= Category.assoc _ _ _)))).symm }
    (fun V r m ↦ by
      revert r m
      intro (r : Γ(U, V.unop)) (m : Γ(M, U.ι ''ᵁ V.unop))
      change (U.ι.appIso V.unop).hom (α.app (op (Over.mk (homOfLE (U.ι_image_le V.unop))))
        ((U.ι.appIso V.unop).inv r • m)) = r * (U.ι.appIso V.unop).hom
          (α.app (op (Over.mk (homOfLE (U.ι_image_le V.unop)))) m)
      rw [hα]
      change (U.ι.appIso V.unop).hom ((U.ι.appIso V.unop).inv r *
        (show Γ(X, U.ι ''ᵁ V.unop) from
          α.app (op (Over.mk (homOfLE (U.ι_image_le V.unop)))) m)) =
        r * (U.ι.appIso V.unop).hom (α.app (op (Over.mk (homOfLE (U.ι_image_le V.unop)))) m)
      rw [map_mul, Iso.inv_hom_id_apply])

lemma dualMk_app {U : X.Opens}
    (α : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ (unitModule X).presheaf)
    (hα : ∀ (W : (Over U)ᵒᵖ) (r : Γ(X, W.unop.left)) (m : Γ(M, W.unop.left)),
      α.app W (r • m) = r • show Γ(unitModule X, W.unop.left) from α.app W m)
    (V : (U : Scheme.{u}).Opens) :
    (M.dualMk α hα).app V = (M.restrictAppIso U.ι V).hom ≫
      α.app (op (Over.mk (homOfLE (U.ι_image_le V)))) ≫
      ((unitModule X).restrictAppIso U.ι V).inv ≫ restrictUnitHomApp U.ι V :=
  rfl

/-- The components of `dualMk α hα` are those of `α`. -/
lemma dualApp_dualMk {U : X.Opens}
    (α : (Over.forget U).op ⋙ M.presheaf ⟶ (Over.forget U).op ⋙ (unitModule X).presheaf)
    (hα : ∀ (W : (Over U)ᵒᵖ) (r : Γ(X, W.unop.left)) (m : Γ(M, W.unop.left)),
      α.app W (r • m) = r • show Γ(unitModule X, W.unop.left) from α.app W m)
    {W : X.Opens} (hW : W ≤ U) :
    M.dualApp (M.dualMk α hα) hW = α.app (op (Over.mk (homOfLE hW))) := by
  have hb : W ≤ U.ι ''ᵁ U.ι ⁻¹ᵁ W := Opens.le_ι_image_ι_preimage hW
  have e := α.naturality (Over.homMk (homOfLE hb) :
    Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ W)))).op
  dsimp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op,
    Over.homMk_left] at e
  ext x
  change (unitModule X).presheaf.map (homOfLE hb).op (restrictUnitInvApp U.ι (U.ι ⁻¹ᵁ W)
    (restrictUnitHomApp U.ι (U.ι ⁻¹ᵁ W) (α.app (op (Over.mk (homOfLE (U.ι_image_le (U.ι ⁻¹ᵁ W)))))
      (M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op x)))) =
    α.app (op (Over.mk (homOfLE hW))) x
  have e' := ConcreteCategory.congr_hom e (M.presheaf.map (homOfLE (U.ι.image_preimage_le W)).op x)
  have hx : M.presheaf.map (homOfLE hb).op (M.presheaf.map
      (homOfLE (U.ι.image_preimage_le W)).op x) = x := by
    rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
    exact congr($(M.presheaf.map_id _) x)
  have hR : ∀ y, restrictUnitInvApp U.ι (U.ι ⁻¹ᵁ W) (restrictUnitHomApp U.ι (U.ι ⁻¹ᵁ W) y) = y :=
    fun y ↦ by rw [← CategoryTheory.comp_apply, restrictUnitHomApp_inv, CategoryTheory.id_apply]
  erw [hR]
  exact e'.symm.trans (congrArg _ hx)

/-- The components of a section of the dual are `𝒪_X`-linear. -/
lemma dualApp_map_smul {U : X.Opens} (φ : M.DualSections U) {W : X.Opens} (hW : W ≤ U)
    (r : Γ(X, W)) (m : Γ(M, W)) :
    M.dualApp φ hW (r • m) = r • show Γ(unitModule X, W) from M.dualApp φ hW m := by
  simp only [dualApp, CategoryTheory.comp_apply, map_smul, smul_restrictAppIso_inv_apply,
    Hom.app_smul, restrictUnitInvApp_smul, smul_restrictAppIso_hom_apply, Iso.hom_inv_id_apply]
  congr 1
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  exact congr($(X.presheaf.map_id _) r)

/-- A section of the dual over `U`, as the family of its components over the opens `W ≤ U`. -/
noncomputable def dualToPresheafHom {U : X.Opens} (φ : M.DualSections U) :
    (presheafHom M.presheaf (unitModule X).presheaf).obj (op U) where
  app W := M.dualApp φ (leOfHom W.unop.hom)
  naturality _ _ g := (dualApp_naturality φ _ g.unop.left).symm

/-- Restriction of sections of the dual is semilinear. -/
lemma dualRestrict_smul {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U)) (φ : M.DualSections U) :
    M.dualRestrict h (r • φ) = X.presheaf.map (homOfLE h).op r • M.dualRestrict h φ := by
  refine dualApp_ext fun W hW ↦ ?_
  ext x
  rw [dualApp_dualRestrict, dualApp_smul, dualApp_smul, dualApp_dualRestrict,
    ← CategoryTheory.comp_apply (X.presheaf.map _), ← Functor.map_comp]
  rfl

variable (M)

/-- The dual sheaf as a presheaf of abelian groups. -/
noncomputable def dualPresheafAb : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (M.DualSections U.unop)
  map {U V} i := AddCommGrpCat.ofHom
    { toFun := M.dualRestrict (leOfHom i.unop)
      map_zero' := by
        ext V : 1
        simp [dualRestrict]
      map_add' φ ψ := by
        ext V : 1
        simp [dualRestrict, restrictFunctor_map_add] }
  map_id _ := AddCommGrpCat.ext fun φ ↦
    dualApp_ext fun _ hW ↦ dualApp_dualRestrict _ φ hW
  map_comp _ _ := AddCommGrpCat.ext fun φ ↦
    dualApp_ext fun _ hW ↦ (dualApp_dualRestrict _ φ hW).trans
      ((dualApp_dualRestrict _ φ _).symm.trans (dualApp_dualRestrict _ _ hW).symm)

/-- The dual presheaf, as a presheaf of types, is the presheaf of `𝒪_X`-linear morphisms
`M|_U ⟶ 𝒪_X|_U` over the opens `U` of `X`. -/
noncomputable def dualPresheafAbCompForgetIso :
    M.dualPresheafAb ⋙ CategoryTheory.forget AddCommGrpCat ≅
    (PresheafOfModules.presheafHomLinearSubfunctor (R := X.presheaf) M.val
      (unitModule X).val).toFunctor :=
  NatIso.ofComponents (fun U ↦ Equiv.toIso
    { toFun φ := ⟨dualToPresheafHom φ, fun W r m ↦
        dualApp_map_smul φ (leOfHom W.unop.hom) r m⟩
      invFun α := M.dualMk α.1 α.2
      left_inv φ := dualApp_ext fun _ hW ↦ dualApp_dualMk _ _ hW
      right_inv α := Subtype.ext (NatTrans.ext (funext fun W ↦ dualApp_dualMk _ _ _)) })
    (fun f ↦ by
      ext φ
      exact Subtype.ext (NatTrans.ext (funext fun W ↦
        dualApp_dualRestrict (leOfHom f.unop) φ (leOfHom W.unop.hom))))

noncomputable instance (U : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (M.dualPresheafAb.obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (M.DualSections U.unop))

/-- The dual sheaf as a presheaf of `𝒪_X`-modules: the restriction maps are semilinear. -/
noncomputable def dualPresheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf M.dualPresheafAb
    (fun _ _ f r φ ↦ dualRestrict_smul (leOfHom f.unop) r φ)

/-- The dual `ℋom_{𝒪_X}(M, 𝒪_X)` of a sheaf of `𝒪_X`-modules `M`: its sections over `U` are the
morphisms `M|_U ⟶ 𝒪_U`. -/
noncomputable def dual : X.Modules where
  val := M.dualPresheaf
  isSheaf := by
    refine Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat.{u}) ?_
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso _ M.dualPresheafAbCompForgetIso.symm
      (PresheafOfModules.isSheaf_presheafHomLinearSubfunctor (unitModule X).isSheaf)

end Modules

/-! ### The cotangent and tangent sheaves of a morphism -/

namespace Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The morphism `f⁻¹𝒪_S ⟶ 𝒪_X` of presheaves of rings on `X` underlying `f : X ⟶ S`: the
adjoint of `f^♯ : 𝒪_S ⟶ f_*𝒪_X`. -/
noncomputable def pullbackPresheafHom :
    (TopCat.Presheaf.pullback CommRingCat.{u} f.base).obj S.presheaf ⟶ X.presheaf :=
  ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).homEquiv _ _).symm f.c

/-- The presheaf of relative differentials of `f : X ⟶ S`: over `U` the Kähler differentials of
`𝒪_X(U)` relative to `(f⁻¹𝒪_S)(U)`. (blueprint: `sk-d-tangent`) -/
noncomputable def cotangentPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' f.pullbackPresheafHom

/-- The universal relative derivation `d : 𝒪_X → Ω` into the presheaf of relative differentials. -/
noncomputable def cotangentPresheafDerivation :
    f.cotangentPresheaf.Derivation' f.pullbackPresheafHom :=
  PresheafOfModules.DifferentialsConstruction.derivation' f.pullbackPresheafHom

/-- The sheaf `Ω¹_{X/S}` of relative differentials of `f : X ⟶ S`: the sheafification of the
presheaf of relative Kähler differentials. (blueprint: `sk-d-tangent`) -/
noncomputable def cotangentSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.cotangentPresheaf

/-- The tangent sheaf `T_{X/S} = ℋom_{𝒪_X}(Ω¹_{X/S}, 𝒪_X)` of `f : X ⟶ S`: the sheaf of relative
vector fields, that is of derivations of `𝒪_X` over `f⁻¹𝒪_S`. (blueprint: `sk-d-tangent`) -/
noncomputable def tangentSheaf : X.Modules :=
  Modules.dual f.cotangentSheaf

/-- The tangent sheaf of `f : X ⟶ S` along a section `e : S ⟶ X`: the dual
`ℋom_{𝒪_S}(e^*Ω¹_{X/S}, 𝒪_S)` of the pullback of the cotangent sheaf, the sheaf of relative
tangent vectors at the points of `e`. For the identity section of a group scheme this is the Lie
algebra sheaf. (blueprint: `sk-d-tangent`) -/
noncomputable def tangentSheafAlong (e : S ⟶ X) : S.Modules :=
  Modules.dual ((Modules.pullback e).obj f.cotangentSheaf)

/-- For a smooth morphism `f` the cotangent sheaf is locally free, so the tangent sheaf along a
section `e` is the pullback `e^*T_{X/S}` of the tangent sheaf.

Proof sketch (not formalised): for a locally free `Ω` of finite rank, `e^*ℋom(Ω, 𝒪_X) ≅
ℋom(e^*Ω, 𝒪_S)`, since both sides commute with finite direct sums and agree for `Ω = 𝒪_X`. -/
theorem tangentSheafAlong_iso_pullback_tangentSheaf [Smooth f] (e : S ⟶ X) (he : e ≫ f = 𝟙 S) :
    Nonempty (f.tangentSheafAlong e ≅ (Modules.pullback e).obj f.tangentSheaf) := by
  sorry

end Hom

end Scheme

end AlgebraicGeometry
