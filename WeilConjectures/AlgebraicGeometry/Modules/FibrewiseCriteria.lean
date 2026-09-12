/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Monoidal
public import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Global sections of a trivial line bundle, read on the fibres

Let `X` be a scheme and `F` a sheaf of `𝒪ₓ`-modules. The fibre `F(x)` of `F` at a point `x` is
the `κ(x)`-vector space `AlgebraicGeometry.Scheme.Modules.fiber`, and a global section `s` of `F`
has an image in it. This file introduces that image,
`AlgebraicGeometry.Scheme.Modules.fiberMk`, and proves the two statements about a *trivial* line
bundle `L ≅ 𝒪ₓ` on a proper integral scheme that the seesaw theorem consumes: the space of
global sections is one-dimensional, and a non-zero global section has non-zero image in every
fibre, i.e. it generates `L` at every point.

The fibre is defined by pullback along `Spec κ(x) ⟶ X`, so the image of a global section in it
is the pullback of sections `AlgebraicGeometry.Scheme.Modules.sectionsPullback` along that
morphism. The computation for a trivial bundle is therefore the computation of the pullback of
sections of the structure sheaf, which is the map on global functions: this is
`AlgebraicGeometry.Scheme.Modules.app_pullbackUnitIso_hom_sectionsPullback`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.fiberMk`: the image `s(x) ∈ F(x)` of a global section `s` of
  a sheaf of `𝒪ₓ`-modules `F` in the fibre at `x`.
- `AlgebraicGeometry.Scheme.Modules.sectionsEquivOfIsoUnit`: an isomorphism `L ≅ 𝒪ₓ` identifies
  `Γ(X, L)` with `Γ(X, 𝒪ₓ)`, so the global sections of a trivial line bundle are a free
  `Γ(X, 𝒪ₓ)`-module of rank one.

## Main results

- `AlgebraicGeometry.Scheme.Modules.finrank_sections_eq_one_of_iso_unit`: for `X` proper and
  integral over an algebraically closed field `k` and `L ≅ 𝒪ₓ`, the space `Γ(X, L)` is a
  one-dimensional `k`-vector space.
- `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_iso_unit` and
  `AlgebraicGeometry.Scheme.Modules.fiberMk_ne_zero_of_iso_unit_of_isProper`: a non-zero global
  section of a trivial line bundle on a scheme whose global functions form a field — for
  instance a proper integral scheme over a field — has non-zero image in the fibre at every
  point, that is, it generates the bundle at every point.

## Blueprint

The two main results together are `lem:cube-nowhere-vanishing` of the theorem-of-the-cube
chapter, `blueprint/src/version/detailed/curve_estimates/27_theorem_of_the_cube.tex`.

The other three statements of that group of four — `lem:cube-degeneracy-closed`,
`lem:cube-invertible-fibrewise` and `lem:cube-triviality-criterion` — are *not* proved here.
Their proofs go through a local trivialisation of a line bundle, and the fact that an invertible
sheaf of modules in the sense of `SheafOfModules.Invertible` is locally isomorphic to the
structure sheaf — that `SheafOfModules.Invertible M` implies that `M` restricted to the members
of some open cover is isomorphic to the structure sheaf — is available neither in Mathlib
`v4.33.1` nor in this project. Those three statements are therefore left to later work, which
has to supply that local trivialisation first.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section SectionsPullback

/-- **The pullback of sections of the structure sheaf is the map on functions.** Under the
identification `a ^* 𝒪ᵧ ≅ 𝒪ₓ` of `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso`, the pullback
of a global section of `𝒪ᵧ` along `a : X ⟶ Y` is its image under `a.appTop`. -/
lemma app_pullbackUnitIso_hom_sectionsPullback (a : X ⟶ Y) (r : Γ(Y, ⊤)) :
    Hom.app (pullbackUnitIso a).hom ⊤ (sectionsPullback a (unit Y.ringCatSheaf) r) =
      a.appTop r := by
  have key : (pullbackPushforwardAdjunction a).unit.app (unit Y.ringCatSheaf) ≫
      (pushforward a).map (pullbackUnitIso a).hom =
        unitToPushforwardObjUnit a.toRingCatSheafHom := by
    have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (φ := a.toRingCatSheafHom)
    rw [Adjunction.homEquiv_unit] at h
    exact h
  have hnat := ((pullbackUnitIso a).hom.mapPresheaf).naturality
    (homOfLE (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)).op
  have h3 := congrArg (fun f ↦ Hom.app f ⊤) key
  rw [Hom.comp_app, pushforward_map_app] at h3
  replace h3 := ConcreteCategory.congr_hom h3 r
  rw [ConcreteCategory.comp_apply] at h3
  rw [sectionsPullback]
  simp only [ConcreteCategory.comp_apply]
  rw [← ConcreteCategory.comp_apply, ← mapPresheaf_app, hnat]
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app]
  exact (congrArg (ConcreteCategory.hom ((presheaf (unit X.ringCatSheaf)).map
    (homOfLE (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)).op)) h3).trans (map_le_top_app_top a r)

/-- The pullback of global sections along `a : X ⟶ Y` is natural in the sheaf of modules. -/
lemma sectionsPullback_naturality (a : X ⟶ Y) {N N' : Y.Modules} (ψ : N ⟶ N') (s : Γ(N, ⊤)) :
    sectionsPullback a N' (Hom.app ψ ⊤ s) =
      Hom.app ((pullback a).map ψ) ⊤ (sectionsPullback a N s) := by
  have hnat := ((pullback a).map ψ).mapPresheaf.naturality
    (homOfLE (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)).op
  have h3 := congrArg (fun f ↦ Hom.app f ⊤) ((pullbackPushforwardAdjunction a).unit.naturality ψ)
  rw [Hom.comp_app, Hom.comp_app, Functor.id_map, Functor.comp_map, pushforward_map_app] at h3
  replace h3 := ConcreteCategory.congr_hom h3 s
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h3
  simp only [sectionsPullback, ConcreteCategory.comp_apply]
  conv_rhs => rw [← ConcreteCategory.comp_apply, ← mapPresheaf_app, hnat]
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app]
  exact congrArg (ConcreteCategory.hom (((pullback a).obj N').presheaf.map
    (homOfLE (by simp : (⊤ : X.Opens) ≤ a ⁻¹ᵁ ⊤)).op)) h3

end SectionsPullback

section FiberMk

/-- The image `s(x) ∈ F(x)` of a global section `s` of a sheaf of `𝒪ₓ`-modules `F` in the fibre
of `F` at a point `x`. The fibre is the global sections of the pullback of `F` along
`Spec κ(x) ⟶ X`, so this is the pullback of sections along that morphism. -/
noncomputable def fiberMk (F : X.Modules) (x : X) (s : Γ(F, ⊤)) : F.fiber x :=
  sectionsPullback (X.fromSpecResidueField x) F s

@[simp]
lemma fiberMk_zero (F : X.Modules) (x : X) : fiberMk F x 0 = 0 :=
  map_zero (ConcreteCategory.hom (sectionsPullback (X.fromSpecResidueField x) F))

lemma fiberMk_add (F : X.Modules) (x : X) (s t : Γ(F, ⊤)) :
    fiberMk F x (s + t) = fiberMk F x s + fiberMk F x t :=
  map_add (ConcreteCategory.hom (sectionsPullback (X.fromSpecResidueField x) F)) s t

/-- The image in the fibre of the image of a global section under a morphism of sheaves of
modules is the image of the section under the induced map on fibres. -/
lemma fiberMap_fiberMk {F G : X.Modules} (ψ : F ⟶ G) (x : X) (s : Γ(F, ⊤)) :
    fiberMap ψ x (fiberMk F x s) = fiberMk G x (Hom.app ψ ⊤ s) := by
  rw [fiberMk, fiberMk, sectionsPullback_naturality]
  rfl

instance (x : X) : Nontrivial Γ(Spec (X.residueField x), ⊤) :=
  (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.toEquiv.nontrivial

/-- **A global function which is a unit does not vanish at any point.** The image in the fibre
`𝒪ₓ(x) = κ(x)` of a unit of `Γ(X, 𝒪ₓ)` is non-zero. -/
lemma fiberMk_unit_ne_zero {r : Γ(X, ⊤)} (hr : IsUnit r) (x : X) :
    fiberMk (unit X.ringCatSheaf) x r ≠ 0 := by
  intro h
  have hu : IsUnit ((X.fromSpecResidueField x).appTop r) := hr.map _
  rw [← app_pullbackUnitIso_hom_sectionsPullback (X.fromSpecResidueField x) r,
    show sectionsPullback (X.fromSpecResidueField x) (unit X.ringCatSheaf) r =
      fiberMk (unit X.ringCatSheaf) x r from rfl, h, map_zero] at hu
  exact zero_ne_one (isUnit_zero_iff.mp hu)

end FiberMk

section Trivial

variable {L : X.Modules}

/-- **The global sections of a trivial line bundle.** If `L ≅ 𝒪ₓ`, then `Γ(X, L)` is a free
`Γ(X, 𝒪ₓ)`-module of rank one: an isomorphism `L ≅ 𝒪ₓ` identifies `Γ(X, L)` with `Γ(X, 𝒪ₓ)`.

Together with `AlgebraicGeometry.isIso_ΓSpecIso_inv_comp_appTop`, which identifies `Γ(X, 𝒪ₓ)`
with `k` for `X` proper and integral over an algebraically closed field `k`, this is the
assertion `dim_k Γ(X, L) = 1` of `lem:cube-nowhere-vanishing`. -/
noncomputable def sectionsEquivOfIsoUnit (e : L ≅ unit X.ringCatSheaf) :
    Γ(L, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) where
  toFun := Hom.app e.hom ⊤
  map_add' := map_add _
  map_smul' r m := Hom.app_smul e.hom r m
  invFun := Hom.app e.inv ⊤
  left_inv m := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id, Hom.id_app]
    rfl
  right_inv m := by
    rw [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.inv_hom_id, Hom.id_app]
    rfl

@[simp]
lemma sectionsEquivOfIsoUnit_apply (e : L ≅ unit X.ringCatSheaf) (s : Γ(L, ⊤)) :
    sectionsEquivOfIsoUnit e s = Hom.app e.hom ⊤ s := rfl

/-- **A non-zero global section of a trivial line bundle vanishes nowhere.** If the ring of
global functions of `X` is a field — for instance if `X` is an integral scheme, proper over a
field — and `L ≅ 𝒪ₓ`, then a non-zero global section of `L` has non-zero image in the fibre
`L(x)` at every point `x`, that is, it generates `L` at every point.

This is the second half of `lem:cube-nowhere-vanishing` of the blueprint. -/
theorem fiberMk_ne_zero_of_iso_unit (hX : IsField Γ(X, ⊤)) (e : L ≅ unit X.ringCatSheaf)
    {s : Γ(L, ⊤)} (hs : s ≠ 0) (x : X) : fiberMk L x s ≠ 0 := by
  intro h
  have hne : sectionsEquivOfIsoUnit e s ≠ 0 :=
    fun hz ↦ hs ((sectionsEquivOfIsoUnit e).map_eq_zero_iff.mp hz)
  have hunit : IsUnit (sectionsEquivOfIsoUnit e s) :=
    isUnit_iff_exists_inv.mpr (hX.mul_inv_cancel hne)
  refine fiberMk_unit_ne_zero hunit x ?_
  rw [sectionsEquivOfIsoUnit_apply, ← fiberMap_fiberMk e.hom x s, h, map_zero]

/-- **The space of global sections of a trivial line bundle on a proper variety is
one-dimensional.** For `X` proper and integral over an algebraically closed field `K` and
`L ≅ 𝒪ₓ`, the `K`-vector space `Γ(X, L)` — for the `K`-structure coming from the structure
morphism `π` — has dimension one. This is the first half of `lem:cube-nowhere-vanishing`. -/
theorem finrank_sections_eq_one_of_iso_unit {K : Type u} [Field K] [IsAlgClosed K]
    (π : X ⟶ Spec (.of K)) [IsIntegral X] [IsProper π] (e : L ≅ unit X.ringCatSheaf) :
    letI : Module K Γ(L, ⊤) :=
      Module.compHom _ ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop).hom
    Module.finrank K Γ(L, ⊤) = 1 := by
  let _ : Module K Γ(L, ⊤) :=
    Module.compHom _ ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop).hom
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop) := isIso_ΓSpecIso_inv_comp_appTop π
  let φ : K ≃+* Γ(X, ⊤) := (asIso ((Scheme.ΓSpecIso (.of K)).inv ≫ π.appTop))
    |>.commRingCatIsoToRingEquiv
  let g : K ≃ₗ[K] Γ(L, ⊤) :=
    { toFun := fun c ↦ (sectionsEquivOfIsoUnit e).symm (φ c)
      map_add' := fun c d ↦ by simp [map_add]
      map_smul' := fun c d ↦ by
        change (sectionsEquivOfIsoUnit e).symm (φ (c * d)) =
          φ c • (sectionsEquivOfIsoUnit e).symm (φ d)
        rw [map_mul, ← smul_eq_mul, LinearEquiv.map_smul]
      invFun := fun m ↦ φ.symm (sectionsEquivOfIsoUnit e m)
      left_inv := fun c ↦ by
        dsimp only
        rw [LinearEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
      right_inv := fun m ↦ by
        dsimp only
        rw [RingEquiv.apply_symm_apply, LinearEquiv.symm_apply_apply] }
  rw [← g.finrank_eq, Module.finrank_self]

/-- **A non-zero global section of a trivial line bundle on a proper integral scheme vanishes
nowhere.** This is `lem:cube-nowhere-vanishing` of the blueprint under its own hypotheses; the
field `K` need not be algebraically closed. -/
theorem fiberMk_ne_zero_of_iso_unit_of_isProper {K : Type u} [Field K] (π : X ⟶ Spec (.of K))
    [IsIntegral X] [IsProper π] (e : L ≅ unit X.ringCatSheaf) {s : Γ(L, ⊤)} (hs : s ≠ 0)
    (x : X) : fiberMk L x s ≠ 0 :=
  fiberMk_ne_zero_of_iso_unit (isField_of_universallyClosed K π) e hs x

variable (X) in
/-- The structure sheaf `𝒪ₓ` is the tensor unit of the monoidal category of `𝒪ₓ`-modules. -/
noncomputable def tensorUnitIsoUnit : 𝟙_ X.Modules ≅ unit X.ringCatSheaf :=
  SheafOfModules.tensorUnitIso X.sheaf

end Trivial

end AlgebraicGeometry.Scheme.Modules
