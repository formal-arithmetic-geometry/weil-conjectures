/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExceptionalGeneral
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.ExternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethVerdierInduction
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!

# The Künneth–Verdier isomorphism on the étale site

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek`
  (`prop-trf-exceptional-kunneth`): the exceptional Künneth map `α` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom`
  (`prop-trf-external-hom`): the external Hom map `β` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_verdierDual`
  (`thm-trf-kunneth-verdier`): the Künneth–Verdier map `κ` is an isomorphism; `β` is deduced
  from `κ` by Verdier biduality.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The Künneth–Verdier map `κ` from the external Hom map `β` and the exceptional Künneth map
`α` (blueprint proof of `thm-trf-kunneth-verdier`): `β` for the pairs `(Λ_X, M)` and
`(N, ω_Y)` gives `RHom(Λ_X, M) ⊠ 𝔻_Y N ≅ RHom(Λ_X ⊠ N, M ⊠ ω_Y)`; the unit identifications
`RHom(Λ_X, M) ≅ M` and `Λ_X ⊠ N ≅ p_Y^* N` and `α : M ⊠ ω_Y ≅ Rp_X^! M` conclude. -/
theorem nonempty_iso_externalProduct_verdierDual_of_iso {S X Y : Scheme.{u}} (a : X ⟶ S)
    (b : Y ⟶ S) [HasCompactification b] [HasCompactification (pullback.fst a b)]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hβ : Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b
        ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op (𝟙_ _))).obj M)
        ((RHom(Y)[ModuleCat.{u + 1} Λ].obj (op N)).obj (dualizingComplex _ b)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op (externalProduct (ModuleCat.{u + 1} Λ) a b (𝟙_ _) N))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b))))
    (hα : Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b) ≅
      (R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M)) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M)) := by
  obtain ⟨β⟩ := hβ
  obtain ⟨α⟩ := hα
  let w : (RHom(X)[ModuleCat.{u + 1} Λ].obj (op (𝟙_ _))).obj M ≅ M :=
    (MonoidalClosed.unitNatIso.app M).symm
  let v : externalProduct (ModuleCat.{u + 1} Λ) a b (𝟙_ _) N ≅
      (L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N :=
    ((derivedTensor _ _).mapIso (leftDerivedUpperStarUnitIso _ (pullback.fst a b))).app _ ≪≫
      λ_ _
  exact ⟨((derivedTensor _ _).mapIso
      ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).mapIso w.symm)).app _ ≪≫ β ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).mapIso v.symm.op).app _ ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso α⟩

/-- The exceptional Künneth map for `𝟙_X × b : X ×_S Y ⟶ X ×_S S` identifies `Rp_X^! M` with
`M ⊠ ω_Y`: given `α : R𝟙^! M ⊠ Rb^! Λ_S ≅ R(𝟙_X × b)^! (M ⊠ Λ_S)`, transporting along
`X ×_S S ≅ X` and `(𝟙 ≫ a) ×_S (b ≫ 𝟙) = X ×_S Y` gives `M ⊠ ω_Y ≅ Rp_X^! M`. -/
theorem nonempty_iso_externalProduct_dualizingComplex_of_iso {S X Y : Scheme.{u}}
    (a : X ⟶ S) (b : Y ⟶ S) [HasCompactification b] [HasCompactification (pullback.fst a b)]
    [QuasiCompact (pullback.fst a b)]
    [HasCompactification (pullback.mapOverBase (𝟙 X) b a (𝟙 S))]
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (h : Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (𝟙 X ≫ a) (b ≫ 𝟙 S)
        ((R(𝟙 X)^![ModuleCat.{u + 1} Λ]).obj M) ((R(b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      (R(pullback.mapOverBase (𝟙 X) b a (𝟙 S))^![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) a (𝟙 S) M (𝟙_ _)))) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M (dualizingComplex _ b) ≅
      (R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M) := by
  obtain ⟨h⟩ := h
  let e : pullback (𝟙 X ≫ a) (b ≫ 𝟙 S) ≅ pullback a b := pullback.congrHom (by simp) (by simp)
  let ψ := pullback.mapOverBase (𝟙 X) b a (𝟙 S)
  let ι : pullback a (𝟙 S) ≅ X := asIso (pullback.fst a (𝟙 S))
  have hψ : e.inv ≫ ψ ≫ ι.hom = pullback.fst a b := by simp [e, ψ, ι]
  have hψ' : e.inv ≫ ψ = pullback.fst a b ≫ ι.inv := by
    rw [← hψ]; simp
  have : HasCompactification (e.inv ≫ ψ) := by
    have : HasCompactification (pullback.fst a b ≫ ι.inv) :=
      HasCompactification.comp_of_isProper _ _
    exact HasCompactification.of_eq hψ'.symm
  have : QuasiCompact (e.inv ≫ ψ) := by rw [hψ']; infer_instance
  have hcomp : pullback.fst a b = (e.inv ≫ ψ) ≫ ι.hom := by rw [Category.assoc, hψ]
  have : HasCompactification ((e.inv ≫ ψ) ≫ ι.hom) := HasCompactification.of_eq hcomp
  have : QuasiCompact ((e.inv ≫ ψ) ≫ ι.hom) := by rw [← hcomp]; infer_instance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ (e.inv ≫ ψ) ι.hom
  obtain ⟨c'⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ e.inv ψ
  obtain ⟨q⟩ := nonempty_iso_rightDerivedUpperShriek_of_eq (A := ModuleCat.{u + 1} Λ) hcomp.symm
  obtain ⟨p⟩ := nonempty_iso_leftDerivedUpperStar_externalProduct_of_comp (ModuleCat.{u + 1} Λ)
    (𝟙 X ≫ a) (b ≫ 𝟙 S) a b (𝟙 X) (𝟙 Y) e.inv (by simp [e]) (by simp [e])
    ((R(𝟙 X)^![ModuleCat.{u + 1} Λ]).obj M) ((R(b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))
  let i₁ : (L((𝟙 X)^*[ModuleCat.{u + 1} Λ])).obj ((R(𝟙 X)^![ModuleCat.{u + 1} Λ]).obj M) ≅ M :=
    (leftDerivedUpperStarId _ X).app _ ≪≫
      (rightDerivedUpperShriekIsoOfIso _ (Iso.refl X)).app M ≪≫ (leftDerivedUpperStarId _ X).app M
  let i₂ : (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).obj ((R(b)^![ModuleCat.{u + 1} Λ]).obj (𝟙_ _)) ≅
      dualizingComplex _ b :=
    (leftDerivedUpperStarId _ Y).app _
  let r : externalProduct (ModuleCat.{u + 1} Λ) a (𝟙 S) M (𝟙_ _) ≅
      (R(ι.hom)^![ModuleCat.{u + 1} Λ]).obj M :=
    ((derivedTensor _ _).obj _).mapIso (leftDerivedUpperStarUnitIso _ _) ≪≫ ρ_ _ ≪≫
      ((rightDerivedUpperShriekIsoOfIso _ ι).app M).symm
  exact ⟨((derivedTensor _ _).mapIso
      ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).mapIso i₁.symm)).app _ ≪≫
    ((derivedTensor _ _).obj _).mapIso
      ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).mapIso i₂.symm) ≪≫ p.symm ≪≫
    (L((e.inv)^*[ModuleCat.{u + 1} Λ])).mapIso h ≪≫
    ((rightDerivedUpperShriekIsoOfIso _ e.symm).app _).symm ≪≫ (c'.app _).symm ≪≫
    (R(e.inv ≫ ψ)^![ModuleCat.{u + 1} Λ]).mapIso r ≪≫ (c.app M).symm ≪≫ q.app M⟩

/-- The product `𝟙_X × b : X ×_S Y ⟶ X ×_S S` admits a compactification when the projection
`p_X : X ×_S Y ⟶ X` does: up to the isomorphisms `(𝟙 ≫ a) ×_S (b ≫ 𝟙) ≅ X ×_S Y` and
`X ×_S S ≅ X` it is `p_X`. -/
lemma hasCompactification_mapOverBase_id {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    [HasCompactification (pullback.fst a b)] :
    HasCompactification (pullback.mapOverBase (𝟙 X) b a (𝟙 S)) := by
  let e : pullback (𝟙 X ≫ a) (b ≫ 𝟙 S) ≅ pullback a b := pullback.congrHom (by simp) (by simp)
  let ι : pullback a (𝟙 S) ≅ X := asIso (pullback.fst a (𝟙 S))
  have : HasCompactification (pullback.fst a b ≫ ι.inv) :=
    HasCompactification.comp_of_isProper _ _
  have : HasCompactification (e.hom ≫ pullback.fst a b ≫ ι.inv) :=
    HasCompactification.comp_of_isOpenImmersion _ _
  refine HasCompactification.of_eq (f := e.hom ≫ pullback.fst a b ≫ ι.inv) ?_
  rw [← cancel_mono ι.hom]
  simp [e, ι]

section Theorems

variable (k : Type u) [Field k] [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `prop-trf-exceptional-kunneth`: Exceptional Künneth; the `α` map.

For morphisms `f₁ : X₁ ⟶ Y₁` and `f₂ : X₂ ⟶ Y₂` admitting compactifications over finite-type
`k`-schemes `Y₁`, `Y₂`, and for `N₁ ∈ Dctf(Y₁, Λ)`, `N₂ ∈ Dctf(Y₂, Λ)`,

`α : Rf₁^! N₁ ⊠ Rf₂^! N₂ ≅ R(f₁ × f₂)^! (N₁ ⊠ N₂)`.

As in the blueprint (`AlgebraicGeometry.Etale.exceptionalKunneth_mapOverBase`): `f₁ × f₂` is
`(f₁ × 𝟙) ∘ (𝟙 × f₂)`, and `f × 𝟙` factors through the graph of `f`, a closed immersion
(supported localization), and a base change of a structure morphism, handled by the constant
coefficient case, itself proved by smooth purity for affine spaces, supported localization for
closed immersions and the open–closed dévissage on the source. -/
theorem nonempty_iso_externalProduct_rightDerivedUpperShriek {X₁ X₂ Y₁ Y₂ : Scheme.{u}}
    (b₁ : Y₁ ⟶ Spec (.of k)) (b₂ : Y₂ ⟶ Spec (.of k))
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsSeparated b₂] [LocallyOfFiniteType b₂] [QuasiCompact b₂]
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) [HasCompactification f₁] [HasCompactification f₂]
    [QuasiCompact f₁] [QuasiCompact f₂]
    [HasCompactification (pullback.mapOverBase f₁ f₂ b₁ b₂)]
    {N₁ : _root_.DerivedCategory (Sheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N₂ : _root_.DerivedCategory (Sheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (h₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₁ N₁)
    (h₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) (f₁ ≫ b₁) (f₂ ≫ b₂)
        ((R(f₁)^![ModuleCat.{u + 1} Λ]).obj N₁) ((R(f₂)^![ModuleCat.{u + 1} Λ]).obj N₂) ≅
      (R(pullback.mapOverBase f₁ f₂ b₁ b₂)^![ModuleCat.{u + 1} Λ]).obj
        (externalProduct (ModuleCat.{u + 1} Λ) b₁ b₂ N₁ N₂)) :=
  exceptionalKunneth_mapOverBase Λ (rightDerivedLowerShriekCompCoherence Λ) b₁ b₂ f₁ f₂ h₁ h₂

/-- Blueprint `thm-trf-kunneth-verdier`: Künneth–Verdier isomorphism; the `κ` map.

For `X`, `Y` separated of finite type over an algebraically closed field `k`, with projections
`p_X`, `p_Y` of `X ×_k Y`, and for `M ∈ Dctf(X, Λ)`, `N ∈ Dctf(Y, Λ)`,

`κ : M ⊠ 𝔻_Y N ≅ RHom(p_Y^* N, Rp_X^! M)`. -/
theorem nonempty_iso_externalProduct_verdierDual [IsAlgClosed k] {X Y : Scheme.{u}}
    (a : X ⟶ Spec (.of k))
    (b : Y ⟶ Spec (.of k)) [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [HasCompactification b] [QuasiCompact b] [HasCompactification (pullback.fst a b)]
    {M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M)
    (hN : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y N) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) a b M
        ((verdierDual (ModuleCat.{u + 1} Λ) b).obj (op N)) ≅
      (RHom(pullback a b)[ModuleCat.{u + 1} Λ].obj
          (op ((L((pullback.snd a b)^*[ModuleCat.{u + 1} Λ])).obj N))).obj
        ((R(pullback.fst a b)^![ModuleCat.{u + 1} Λ]).obj M)) := by
  have hE := rightDerivedLowerShriekCompCoherence Λ
  have hD := constructibleFiniteTor_verdierDual Λ b hN
  have hω : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y (dualizingComplex _ b) :=
    constructibleFiniteTor_dualizingComplex Λ (𝟙 _) b (constructibleFiniteTor_tensorUnit Λ _)
  have := isIso_kunnethVerdierMap Λ b N (dualizingComplex _ b) hE hD hω a hM
  obtain ⟨e⟩ := nonempty_iso_rightDerivedUpperShriek_of_isPullback Λ hE b a (pullback.snd a b)
    (pullback.fst a b) (IsPullback.of_hasPullback a b).flip hM
  obtain ⟨fl⟩ := nonempty_iso_derivedTensor_flip (ModuleCat.{u + 1} Λ) (pullback a b)
  exact ⟨asIso (kunnethVerdierMap (ModuleCat.{u + 1} Λ) N (dualizingComplex _ b) (pullback.snd a b)
      ((L((pullback.fst a b)^*[ModuleCat.{u + 1} Λ])).obj M)) ≪≫
    ((RHom(pullback a b)[ModuleCat.{u + 1} Λ]).obj _).mapIso ((fl.app _).app _ ≪≫ e.symm)⟩

/-- Blueprint `prop-trf-external-hom`: External Hom; the `β` map.

For `Z₁`, `Z₂` separated of finite type over an algebraically closed field `k` and
`E₁, N₁ ∈ Dctf(Z₁, Λ)`, `E₂, N₂ ∈ Dctf(Z₂, Λ)`,

`β : RHom(E₁, N₁) ⊠ RHom(E₂, N₂) ≅ RHom(E₁ ⊠ E₂, N₁ ⊠ N₂)`.

By Verdier biduality the Künneth–Verdier isomorphism
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_verdierDual`) says that Verdier duality
commutes with external products, and `RHom(E, N) ≅ 𝔻(𝔻N ⊗ E)`
(`AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom_of_kunnethVerdier`). -/
theorem nonempty_iso_externalProduct_derivedHom [IsAlgClosed k] {Z₁ Z₂ : Scheme.{u}}
    (c₁ : Z₁ ⟶ Spec (.of k)) (c₂ : Z₂ ⟶ Spec (.of k))
    [IsSeparated c₁] [LocallyOfFiniteType c₁] [QuasiCompact c₁]
    [IsSeparated c₂] [LocallyOfFiniteType c₂] [QuasiCompact c₂]
    {E₁ N₁ : _root_.DerivedCategory (Sheaf Z₁.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {E₂ N₂ : _root_.DerivedCategory (Sheaf Z₂.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hE₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ E₁)
    (hE₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ E₂)
    (hN₁ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₁ N₁)
    (hN₂ : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Z₂ N₂) :
    Nonempty (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂
        ((RHom(Z₁)[ModuleCat.{u + 1} Λ].obj (op E₁)).obj N₁)
        ((RHom(Z₂)[ModuleCat.{u + 1} Λ].obj (op E₂)).obj N₂) ≅
      (RHom(pullback c₁ c₂)[ModuleCat.{u + 1} Λ].obj
          (op (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ E₁ E₂))).obj
        (externalProduct (ModuleCat.{u + 1} Λ) c₁ c₂ N₁ N₂)) :=
  nonempty_iso_externalProduct_derivedHom_of_kunnethVerdier Λ c₁ c₂
    (fun hM hN ↦ nonempty_iso_externalProduct_verdierDual Λ k c₁ c₂ hM hN) hE₁ hE₂ hN₁ hN₂

end Theorems

end Etale

end AlgebraicGeometry
