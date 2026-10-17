/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale

/-!
# Smooth duality from the étale and the affine-space cases

The reduction step of the proof of orientation-free smooth duality (blueprint
`thm-asd-smooth-tensor`): for `f : X ⟶ Y` smooth of relative dimension `d`, admitting a
compactification, with the exponent of `Λ` invertible on `X`, the dualizing complex `ω_f` is a
locally constant sheaf of free rank-one `Λ`-modules placed in degree `-2d` and the canonical
tensor map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an isomorphism for every `K`, *provided* this
holds for

* étale morphisms, with `ω_e ≅ Λ` (`AlgebraicGeometry.Etale.EtaleSmoothDuality`): this is the
  étale adjoint locality `lem-amb-etale-adjoint-locality`, `Re^! ≅ Le^*`, together with its
  compatibility with the tensor maps;
* the projections `p_d : 𝔸^d_S ⟶ S` of relative affine space over affine bases `S` on which the
  exponent of `Λ` is invertible (`AlgebraicGeometry.Etale.AffineSpaceSmoothDuality`): this is the
  affine-space adjunction `Rp_{d!} ⊣ p_d^*(d)[2d]` (`cor-amb-affine-space-adjunction`), together
  with its compatibility with the tensor maps.

As in the blueprint, every point of `X` has an affine open neighbourhood `V` on which `f` is the
composite `V --e--> 𝔸^d_U --p_d--> U ⊆ Y` of an étale morphism, an affine-space projection over an
affine open `U` of `Y` and an open immersion (`sbc-thm-etale-local-normal-form`,
`AlgebraicGeometry.Smooth.exists_etale_to_affineSpace`). The canonical tensor maps compose
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_comp_of_forall`) and descend along the
open cover by these neighbourhoods
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_jointlySurjective`); the shape of
the dualizing complex descends as well
(`AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem.of_jointlySurjective`). The exponent of
`Λ` is first made invertible on the base by restricting `Y` to the open subscheme where it is a
unit, through which `f` factors.

## Main definitions

- `AlgebraicGeometry.Etale.EtaleSmoothDuality`
- `AlgebraicGeometry.Etale.AffineSpaceSmoothDuality`
- `AlgebraicGeometry.Etale.SatisfiesSmoothDuality`

## Main statements

- `AlgebraicGeometry.Etale.satisfiesSmoothDuality_of_etaleSmoothDuality_of_affineSpaceSmoothDuality`
- `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor_of_etale_of_affineSpace`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

variable [Finite Λ]

/-- *Smooth duality for étale morphisms*: for every quasi-compact étale morphism `e : V ⟶ W`
admitting a compactification, with the exponent of `Λ` invertible on `V`, the canonical tensor
map `θ_{e,K} : ω_e ⊗ᴸ Le^* K ⟶ Re^! K` is an
isomorphism for every `K`, and the dualizing complex is trivial, `ω_e ≅ Λ_V`. Together this says
that `Re^! ≅ Le^*` through the canonical maps: the étale adjoint locality
`lem-amb-etale-adjoint-locality` with its compatibility with the tensor maps. -/
def EtaleSmoothDuality : Prop :=
  ∀ ⦃V W : Scheme.{u}⦄ (e : V ⟶ W) [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e]
    [HasCompactification e] [HasInvertibleExponent Λ V],
    (∀ K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (dualizingComplexTensorMap Λ e K)) ∧
      Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) e ≅ 𝟙_ _)

/-- *Smooth duality for affine-space projections*: for every affine scheme `S` on which the
exponent of `Λ` is invertible and every `d`, the projection `p_d : 𝔸^d_S ⟶ S` has canonical
tensor map `θ_{p_d,K}` invertible for every `K`, and its dualizing complex is a locally constant
sheaf of free rank-one `Λ`-modules placed in degree `-2d`. This is what the affine-space
adjunction `Rp_{d!} ⊣ p_d^*(d)[2d]` (`cor-amb-affine-space-adjunction`) gives, together with its
compatibility with the tensor maps. -/
def AffineSpaceSmoothDuality : Prop :=
  ∀ (d : ℕ) (S : Scheme.{u}) [IsAffine S] [HasInvertibleExponent Λ S],
    (∀ K : _root_.DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (dualizingComplexTensorMap Λ (𝔸(ULift.{u} (Fin d); S) ↘ S) K)) ∧
      IsShiftedRankOneLocalSystem
        (dualizingComplex (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); S) ↘ S)) (2 * d : ℤ)

/-- A morphism `g` admitting a compactification *satisfies smooth duality in degree `-n`* if its
dualizing complex `ω_g` is a shifted rank-one local system in degree `-n`
(`AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem`) and its canonical tensor maps
`θ_{g,K} : ω_g ⊗ᴸ Lg^* K ⟶ Rg^! K` are isomorphisms for all `K`. The compactification is
quantified over, so that the property does not depend on how it is provided. -/
def SatisfiesSmoothDuality {W Y : Scheme.{u}} (g : W ⟶ Y) (n : ℤ) : Prop :=
  ∀ [HasCompactification g],
    IsShiftedRankOneLocalSystem (dualizingComplex (ModuleCat.{u + 1} Λ) g) n ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (dualizingComplexTensorMap Λ g K)

variable {Λ}

lemma EtaleSmoothDuality.isInvertible (hE : EtaleSmoothDuality Λ) {V W : Scheme.{u}}
    (e : V ⟶ W) [_root_.AlgebraicGeometry.Etale e] [QuasiCompact e] [HasCompactification e]
    [HasInvertibleExponent Λ V] :
    DerivedCategory.isInvertible Λ V (dualizingComplex (ModuleCat.{u + 1} Λ) e) :=
  DerivedCategory.isInvertible.of_iso (hE e).2.some.symm (DerivedCategory.isInvertible_unit Λ V)

/-- Smooth duality for open immersions, which need not be quasi-compact: for an open immersion
`j : U ⟶ X`, with the exponent of `Λ` invertible on `U`, the canonical tensor maps `θ_{j,K}`
are isomorphisms and `ω_j ≅ Λ_U`
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_isOpenImmersion`). -/
lemma smoothDuality_of_isOpenImmersion {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    [HasCompactification j] [HasInvertibleExponent Λ U] :
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      IsIso (dualizingComplexTensorMap Λ j K)) ∧
      Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) j ≅ 𝟙_ _) :=
  ⟨isIso_dualizingComplexTensorMap_of_isOpenImmersion j,
    nonempty_dualizingComplex_iso_of_isOpenImmersion j⟩

variable (Λ) in
/-- **Smooth duality for étale morphisms** holds
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_etale`,
`AlgebraicGeometry.Etale.nonempty_dualizingComplex_iso_of_etale`). -/
theorem etaleSmoothDuality : EtaleSmoothDuality Λ := fun _ _ e _ _ _ _ ↦
  ⟨isIso_dualizingComplexTensorMap_of_etale e, nonempty_dualizingComplex_iso_of_etale e⟩

/-- Smooth duality glues along open covers: if every point `x` of `X` lies in an open subscheme
`u : W ⟶ X` such that `u ≫ f` satisfies smooth duality in degree `-n`, then so does `f`. The
canonical tensor maps descend along the cover
(`AlgebraicGeometry.Etale.isIso_dualizingComplexTensorMap_of_jointlySurjective`), and so does the
shape of the dualizing complex
(`AlgebraicGeometry.Etale.IsShiftedRankOneLocalSystem.of_jointlySurjective`), through
`ω_{u ≫ f} ≅ Lu^* ω_f`. -/
theorem satisfiesSmoothDuality_of_forall_exists_isOpenImmersion {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] (f : X ⟶ Y) (n : ℤ)
    (h : ∀ x : X, ∃ (W : Scheme.{u}) (u : W ⟶ X), IsOpenImmersion u ∧ x ∈ Set.range u.base ∧
      SatisfiesSmoothDuality Λ (u ≫ f) n) :
    SatisfiesSmoothDuality Λ f n := by
  intro _
  choose W u hu hx hg using h
  have (x : X) : HasCompactification (u x) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  have (x : X) : HasCompactification (u x ≫ f) :=
    ((HasCompactification.compactification f).precomp (u x)).hasCompactification
  have hg' (x : X) := @hg x (this x)
  have (x : X) : HasInvertibleExponent Λ (W x) := .of_hom (u x)
  have hsurj (x : X) : ∃ (i : X) (y : W i), (u i).base y = x := by
    obtain ⟨y, hy⟩ := hx x
    exact ⟨x, y, hy⟩
  refine ⟨IsShiftedRankOneLocalSystem.of_jointlySurjective u hsurj fun x ↦ ?_,
    fun K ↦ isIso_dualizingComplexTensorMap_of_jointlySurjective Λ u hsurj f
      (fun x ↦ (smoothDuality_of_isOpenImmersion (u x)).1)
      (fun x ↦ isInvertible_dualizingComplex_of_isOpenImmersion (u x)) K fun x ↦ (hg' x).2 K⟩
  obtain ⟨e⟩ := nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar Λ (u x) f _ rfl
    ((smoothDuality_of_isOpenImmersion (u x)).1 _) (smoothDuality_of_isOpenImmersion (u x)).2
  exact (hg' x).1.of_iso e

section Chart

variable (hE : EtaleSmoothDuality Λ) (hA : AffineSpaceSmoothDuality Λ)
include hE hA

/-- Smooth duality on a chart of the étale-local normal form: if `f` restricted to an affine open
`V` of `X` is the composite `V --e--> 𝔸^d_U --p_d--> U ⊆ Y` of an étale morphism, an
affine-space projection over an affine open `U` of `Y` on which the exponent of `Λ` is invertible
and an open immersion, then `V ⟶ Y` satisfies smooth duality in degree `-2d`. -/
theorem satisfiesSmoothDuality_chart {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) {U : Y.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
    (e : V.toScheme ⟶ 𝔸(ULift.{u} (Fin d); U.toScheme)) [_root_.AlgebraicGeometry.Etale e]
    (hfe : e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) = f.resLE U V hVU)
    [HasInvertibleExponent Λ U.toScheme] :
    SatisfiesSmoothDuality Λ (V.ι ≫ f) (2 * d : ℤ) := by
  intro _
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  have : HasCompactification e := HasCompactification.of_isQuasiAffine e
  have : HasCompactification (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme)) :=
    HasCompactification.of_isQuasiAffine _
  have : HasCompactification U.ι := (Compactification.ofIsOpenImmersion _).hasCompactification
  have : HasInvertibleExponent Λ V.toScheme := .of_hom (f.resLE U V hVU)
  obtain ⟨hθe, hωe⟩ := hE e
  obtain ⟨hθι, hωι⟩ := smoothDuality_of_isOpenImmersion (Λ := Λ) U.ι
  obtain ⟨hθp, hωp⟩ := hA d U.toScheme
  -- the composite `q = e ≫ p_d : V ⟶ U`
  have hθq (K) : IsIso (dualizingComplexTensorMap Λ
      (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme)) K) :=
    isIso_dualizingComplexTensorMap_comp_of_forall Λ e
      (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) _ rfl hθe hωp.isInvertible K (hθp K)
  have hωq : IsShiftedRankOneLocalSystem (dualizingComplex (ModuleCat.{u + 1} Λ)
      (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme))) (2 * d : ℤ) := by
    obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_leftDerivedUpperStar Λ e
      (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme) _ rfl (hθe _) hωe
    exact (hωp.leftDerivedUpperStar e).of_iso c.symm
  -- the composite `q ≫ U.ι = V.ι ≫ f`
  have w : (e ≫ (𝔸(ULift.{u} (Fin d); U.toScheme) ↘ U.toScheme)) ≫ U.ι = V.ι ≫ f := by
    rw [hfe, Scheme.Hom.resLE_comp_ι]
  refine ⟨?_, fun K ↦ isIso_dualizingComplexTensorMap_comp_of_forall Λ _ U.ι _ w hθq
    (isInvertible_dualizingComplex_of_isOpenImmersion U.ι) K (hθι K)⟩
  obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_of_unit Λ _ U.ι _ w (hθq _) hωι
  exact hωq.of_iso c.symm

/-- Smooth duality over a base on which the exponent of `Λ` is invertible: glue the charts of
the étale-local normal form (`AlgebraicGeometry.Etale.satisfiesSmoothDuality_chart`) along the
open cover of `X` by their sources. -/
theorem satisfiesSmoothDuality_of_hasInvertibleExponent {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f] :
    SatisfiesSmoothDuality Λ f (2 * d : ℤ) := by
  have : HasInvertibleExponent Λ X := .of_hom f
  refine satisfiesSmoothDuality_of_forall_exists_isOpenImmersion f _ fun x ↦ ?_
  obtain ⟨U, V, hU, hV, -, hxV, hVU, e, he, hfe⟩ := Smooth.exists_etale_to_affineSpace f d x
  have : HasInvertibleExponent Λ U.toScheme := .of_hom U.ι
  exact ⟨V.toScheme, V.ι, inferInstance, ⟨⟨x, hxV⟩, rfl⟩,
    satisfiesSmoothDuality_chart hE hA f d hU hV hVU e hfe⟩

/-- **Smooth duality from the étale and affine-space cases** (the reduction in the proof of
blueprint `thm-asd-smooth-tensor`): if étale morphisms and affine-space projections satisfy
smooth duality (`AlgebraicGeometry.Etale.EtaleSmoothDuality`,
`AlgebraicGeometry.Etale.AffineSpaceSmoothDuality`), then so does every smooth morphism
`f : X ⟶ Y` of relative dimension `d` with the exponent of `Λ` invertible on `X`, in degree
`-2d`.

The morphism `f` factors through the open subscheme `Y'` of `Y` on which the exponent `n` of `Λ`
is a unit, `f = f' ≫ ι`, as `n` is a unit on `X`; the base change `f'` of `f` is smooth and
satisfies smooth duality by the étale-local normal form
(`AlgebraicGeometry.Etale.satisfiesSmoothDuality_of_hasInvertibleExponent`), and the canonical
tensor maps compose with those of the open immersion `ι`. -/
theorem satisfiesSmoothDuality_of_etaleSmoothDuality_of_affineSpaceSmoothDuality
    {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] (f : X ⟶ Y) (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    SatisfiesSmoothDuality Λ f (2 * d : ℤ) := by
  intro _
  obtain ⟨n, hn, hnΛ, hnX⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  let Y' : Y.Opens := Y.basicOpen (n : Γ(Y, ⊤))
  have : HasInvertibleExponent Λ Y'.toScheme := by
    refine ⟨n, hn, hnΛ, ?_⟩
    have h := RingedSpace.isUnit_res_basicOpen Y.toRingedSpace (n : Γ(Y, ⊤))
    have hle : Y'.ι ''ᵁ ⊤ ≤ Y.basicOpen (n : Γ(Y, ⊤)) := by simp [Y']
    rw [← map_natCast Y'.ι.appTop.hom, Scheme.Opens.ι_appTop]
    have h' := h.map (Y.presheaf.map (homOfLE hle).op).hom
    erw [← CommRingCat.comp_apply, ← Functor.map_comp] at h'
    exact h'
  have hf : Set.range f.base ⊆ Set.range Y'.ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change x ∈ f ⁻¹ᵁ Y.basicOpen (n : Γ(Y, ⊤))
    rw [Scheme.preimage_basicOpen, map_natCast, X.basicOpen_of_isUnit hnX]
    trivial
  have sq := IsOpenImmersion.isPullback_lift_id f Y'.ι hf
  have w : IsOpenImmersion.lift Y'.ι f hf ≫ Y'.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : HasCompactification (IsOpenImmersion.lift Y'.ι f hf) := .of_isPullback sq.flip
  have : SmoothOfRelativeDimension d (IsOpenImmersion.lift Y'.ι f hf) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback sq.flip
      ‹SmoothOfRelativeDimension d f›
  have : HasCompactification Y'.ι := (Compactification.ofIsOpenImmersion _).hasCompactification
  obtain ⟨hω', hθ'⟩ := satisfiesSmoothDuality_of_hasInvertibleExponent hE hA
    (IsOpenImmersion.lift Y'.ι f hf) d
  refine ⟨?_, fun K ↦ isIso_dualizingComplexTensorMap_comp_of_forall Λ _ Y'.ι f w hθ'
    (isInvertible_dualizingComplex_of_isOpenImmersion _) K
    ((smoothDuality_of_isOpenImmersion Y'.ι).1 K)⟩
  obtain ⟨c⟩ := nonempty_dualizingComplex_comp_iso_of_unit Λ _ Y'.ι f w (hθ' _)
    (smoothDuality_of_isOpenImmersion Y'.ι).2
  exact hω'.of_iso c.symm

/-- **Smooth duality from the étale and affine-space cases**, in the form of blueprint
`thm-asd-smooth-tensor` (`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`): if
étale morphisms and affine-space projections satisfy smooth duality, then for every smooth
`f : X ⟶ Y` of relative dimension `d` admitting a compactification, with the exponent of `Λ`
invertible on `X`, `ω_f ≅ L[2d]` for a locally constant sheaf `L` of free rank-one `Λ`-modules
and `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K` is an isomorphism for every `K`. -/
theorem exists_dualizingComplex_iso_and_tensor_of_etale_of_affineSpace {X Y : Scheme.{u}}
    [HasInvertibleExponent Λ X] (f : X ⟶ Y) [HasCompactification f] (d : ℕ)
    [SmoothOfRelativeDimension d f] :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * d : ℤ)⟧) ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (dualizingComplexTensorMap Λ f K) := by
  obtain ⟨⟨L, hL, hs, e⟩, hθ⟩ :=
    satisfiesSmoothDuality_of_etaleSmoothDuality_of_affineSpaceSmoothDuality hE hA f d
  exact ⟨L, hL, hs, e, hθ⟩

end Chart

end Etale

end AlgebraicGeometry
