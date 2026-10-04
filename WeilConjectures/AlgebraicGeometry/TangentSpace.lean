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

- `AlgebraicGeometry.Scheme.Hom.tangentSheafAlong_iso_pullback_tangentSheaf`: for smooth `f`,
  the tangent sheaf along a section is the pullback of the tangent sheaf.

## Blueprint

- `sk-d-tangent`: the tangent space of a point as the dual of the cotangent space `𝔪_x/𝔪_x²`.
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace

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
  map_id := by sorry
  map_comp := by sorry

noncomputable instance (U : (X.Opens)ᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) (M.dualPresheafAb.obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (M.DualSections U.unop))

/-- The dual sheaf as a presheaf of `𝒪_X`-modules: the restriction maps are semilinear. -/
noncomputable def dualPresheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf M.dualPresheafAb (fun _ _ _ _ _ ↦ by sorry)

/-- The dual `ℋom_{𝒪_X}(M, 𝒪_X)` of a sheaf of `𝒪_X`-modules `M`: its sections over `U` are the
morphisms `M|_U ⟶ 𝒪_U`. -/
noncomputable def dual : X.Modules where
  val := M.dualPresheaf
  isSheaf := by sorry

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
