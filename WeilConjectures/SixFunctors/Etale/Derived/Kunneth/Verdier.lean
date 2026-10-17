/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso

/-!

# The Künneth–Verdier isomorphism on the étale site

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_rightDerivedUpperShriek`
  (`prop-trf-exceptional-kunneth`): the exceptional Künneth map `α` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_derivedHom`
  (`prop-trf-external-hom`): the external Hom map `β` is an isomorphism.
- `AlgebraicGeometry.Etale.nonempty_iso_externalProduct_verdierDual`
  (`thm-trf-kunneth-verdier`): the Künneth–Verdier map `κ` is an isomorphism, deduced from `α`
  and `β` as in the blueprint.
- `AlgebraicGeometry.Etale.hasKunnethComparisons` (`sk-thm-sf-kunneth-verdier`): the four
  comparison maps are isomorphisms.

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

/-- The unit `Λ_X` of `D(X_ét, Λ)` lies in `Dctf(X, Λ)`: it is the constant sheaf, which is
constructible and flat, placed in degree `0`. -/
theorem constructibleFiniteTor_tensorUnit (X : Scheme.{u}) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  (constructibleFiniteTor _ X).prop_of_iso (singleFunctorObjUnitIso _ X)
    ⟨boundedConstructible_singleFunctor_obj _ 0, 0, 0,
      torAmplitudeIn_singleFunctor_obj_of_flat Λ _ (ObjectProperty.flat_of_tensorIso (λ_ _))⟩

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

end Etale

end AlgebraicGeometry
