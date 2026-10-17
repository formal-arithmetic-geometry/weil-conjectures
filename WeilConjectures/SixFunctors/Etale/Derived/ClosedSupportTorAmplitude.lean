/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.ConstantTensorProjection
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-!
# Finite Tor amplitude of the exceptional inverse image along a closed immersion

Let `i : Z ⟶ T` be a closed immersion with quasi-compact open complement `j : U ⟶ T`, and `Λ`
a finite ring. If `(U, T)` satisfies the open-complement condition with constant `c`
(`AlgebraicGeometry.Etale.OpenComplementCondition`), then `Ri^!` carries bounded constructible
complexes of Tor amplitude in `[a, b]` to bounded constructible complexes of Tor amplitude in
`[a, b + c + 1]`
(`AlgebraicGeometry.Etale.boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek`,
blueprint `prop-exc-closed-tor`).

Let `κ = Λ ⧸ J` for the Jacobson radical `J`. Tensoring the supported localization triangle
`Ri_! Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶` with the constant complex `κ_T`, the third term becomes
`Rj_*(j^* K ⊗ᴸ κ_U)` by the projection formula with a finite constant coefficient
(`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat`,
`lem-exc-constant-tensor`; `Rj_*` preserves coproducts, having finite cohomological dimension), so
it has homology in `[a, b + c]`; hence `Ri_! Ri^! K ⊗ᴸ κ_T ≅ Ri_!(Ri^! K ⊗ᴸ κ_Z)` has homology in
`[a, b + c + 1]`, and so does `Ri^! K ⊗ᴸ κ_Z`. The residue test
(`AlgebraicGeometry.Etale.DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn`,
`lem-exc-residue-tor-test`) concludes.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {Z T U : Scheme.{u}}

omit [Finite Λ] in
/-- Under the vanishing clause of the open-complement condition, a quasi-compact open immersion
has finite cohomological dimension, so `Rj_*` preserves countable coproducts
(`AlgebraicGeometry.Etale.preservesCoproducts_rightDerivedLowerStar`). -/
lemma preservesColimitsOfShape_rightDerivedLowerStar_of_isZero_higherDirectImage
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M)) :
    PreservesColimitsOfShape (Discrete ℕ) (R((j)_*[ModuleCat.{u + 1} Λ])) :=
  have := preservesCoproducts_rightDerivedLowerStar Λ j (⟨c, fun F q hq ↦ by
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by lia⟩
    exact (hc F n (by exact_mod_cast hq)).of_iso
      (homologyRightDerivedLowerStarSingleIsoHigherDirectImage Λ j F n)⟩) (ULift.{u + 1} ℕ)
  preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) _

variable (Λ) in
/-- The projection formula for a morphism `f` admitting a compactification, at finite
coefficients, as an isomorphism `Rf_! N ⊗ᴸ L ≅ Rf_!(N ⊗ᴸ Lf^* L)`
(`AlgebraicGeometry.Etale.isIso_projectionMap_of_finite`). -/
noncomputable def rightDerivedLowerShriekProjectionIso (f : Z ⟶ T) [HasCompactification f]
    (N : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (L : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    ((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj N)).obj L ≅
      (R(f)_![ModuleCat.{u + 1} Λ]).obj
        (((-⊗ᴸ-(Z)[ModuleCat.{u + 1} Λ]).obj N).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj L)) :=
  have := isIso_projectionMap_of_finite Λ f
  asIso (((projectionMap (ModuleCat.{u + 1} Λ) f).app N).app L)

set_option maxHeartbeats 1000000 in
/-- If `K ⊗ᴸ κ_T` has homology in `[a, b]` for a finitely generated `κ` and `R^q j_*` vanishes
above `c`, then `Rj_* j^* K ⊗ᴸ κ_T ≅ Rj_*(j^* K ⊗ᴸ κ_U)` has homology in `[a, b + c]`, by the
projection formula with a finite constant coefficient. -/
lemma homologyConcentratedIn_derivedTensor_rightDerivedLowerStar_constantSingle
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j] {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} (K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (κ : ModuleCat.{u + 1} Λ) [Module.Finite Λ κ]
    (hK : _root_.DerivedCategory.homologyConcentratedIn a b
      (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj K).obj (constantSingle _ T κ))) :
    _root_.DerivedCategory.homologyConcentratedIn a (b + c)
      (((-⊗ᴸ-(T)[ModuleCat.{u + 1} Λ]).obj ((R((j)_*[ModuleCat.{u + 1} Λ])).obj
        ((L((j)^*[ModuleCat.{u + 1} Λ])).obj K))).obj (constantSingle _ T κ)) := by
  let A := ModuleCat.{u + 1} Λ
  have := preservesColimitsOfShape_rightDerivedLowerStar_of_isZero_higherDirectImage j hc
  obtain ⟨hKa, hKb⟩ := hK
  let C' := (L((j)^*[A])).obj K
  have hproj := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle_of_nat Λ j C' κ
  let W := ((-⊗ᴸ-(U)[A]).obj C').obj ((L((j)^*[A])).obj (constantSingle A T κ))
  have eW : (L((j)^*[A])).obj (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ)) ≅ W :=
    leftDerivedUpperStarTensorIso A j _ _
  have e' := (leftDerivedUpperStarIsoMapDerivedCategory A j).app
    (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ))
  have : (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ)).IsGE a := hKa
  have : (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ)).IsLE b := hKb
  have : (D((j)^*[A]).obj (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ))).IsGE a :=
    Functor.isGE_mapDerivedCategory_obj _ _ a
  have : (D((j)^*[A]).obj (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ))).IsLE b :=
    Functor.isLE_mapDerivedCategory_obj _ _ b
  have : W.IsGE a := _root_.DerivedCategory.TStructure.t.isGE_of_iso (e'.symm ≪≫ eW) a
  have : W.IsLE b := _root_.DerivedCategory.TStructure.t.isLE_of_iso (e'.symm ≪≫ eW) b
  have : ((R((j)_*[A])).obj W).IsGE a := isGE_rightDerivedLowerStar_obj Λ j _ a
  have : ((R((j)_*[A])).obj W).IsLE (b + c) :=
    isLE_rightDerivedLowerStar_obj_of_isZero_higherDirectImage hc _ b
  let eC : ((-⊗ᴸ-(T)[A]).obj ((R((j)_*[A])).obj C')).obj (constantSingle A T κ) ≅
      (R((j)_*[A])).obj W :=
    asIso (((rightDerivedLowerStarProjectionMap A j).app C').app (constantSingle A T κ))
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso eC.symm a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso eC.symm (b + c)⟩

/-- In a distinguished triangle `X₁ ⟶ X₂ ⟶ X₃ ⟶ X₁[1]` of `D(T_ét)`, if `X₂` has homology in
`[a, b]` and `X₃` in `[a, b']` with `b ≤ b'`, then `X₁` has homology in `[a, b' + 1]`. -/
lemma homologyConcentratedIn_obj₁_of_distTriang
    (Tr : Triangle (_root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))))
    (hTr : Tr ∈ distTriang _) {a b b' : ℤ} (hbb : b ≤ b')
    (h₂ : _root_.DerivedCategory.homologyConcentratedIn a b Tr.obj₂)
    (h₃ : _root_.DerivedCategory.homologyConcentratedIn a b' Tr.obj₃) :
    _root_.DerivedCategory.homologyConcentratedIn a (b' + 1) Tr.obj₁ := by
  have hT := inv_rot_of_distTriang _ hTr
  haveI := h₃.1
  haveI := h₃.2
  haveI := h₂.1
  haveI := h₂.2
  have : (Tr.obj₃⟦(-1 : ℤ)⟧).IsGE (a + 1) :=
    _root_.DerivedCategory.TStructure.t.isGE_shift _ a (-1) (a + 1)
  have : (Tr.obj₃⟦(-1 : ℤ)⟧).IsLE (b' + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_shift _ b' (-1) (b' + 1)
  have h₁ : (Tr.invRotate.obj₁).IsGE a :=
    _root_.DerivedCategory.TStructure.t.isGE_of_ge (Tr.obj₃⟦(-1 : ℤ)⟧) a (a + 1) (by lia)
  have h₁' : (Tr.invRotate.obj₁).IsLE (b' + 1) := inferInstanceAs ((Tr.obj₃⟦(-1 : ℤ)⟧).IsLE _)
  have h₃' : (Tr.invRotate.obj₃).IsLE (b' + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_le Tr.obj₂ b (b' + 1) (by lia)
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE₂ _ hT a h₁ h₂.1,
    _root_.DerivedCategory.TStructure.t.isLE₂ _ hT (b' + 1) h₁' h₃'⟩

variable (i : Z ⟶ T) (j : U ⟶ T) [IsClosedImmersion i] [HasCompactification i] [IsOpenImmersion j]
  [QuasiCompact j] (hij : Set.range i.base = (Set.range j.base)ᶜ)

include hij in
set_option maxHeartbeats 1000000 in
/-- The Tor amplitude part of blueprint `prop-exc-closed-tor`: under the vanishing clause of the
open-complement condition with constant `c`, `Ri^!` carries complexes of Tor amplitude in
`[a, b]` to complexes of Tor amplitude in `[a, b + c + 1]`, for a finite ring `Λ`. No
constructibility is needed. -/
theorem torAmplitudeIn_rightDerivedUpperShriek {c : ℕ}
    (hc : ∀ (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ), c < q →
      IsZero (higherDirectImage Λ j q M))
    {a b : ℤ} {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1) ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) := by
  let A := ModuleCat.{u + 1} Λ
  let κ : A := ModuleCat.of Λ (Λ ⧸ Ring.jacobson Λ)
  let N := (R(i)^![A]).obj K
  rw [DerivedCategory.torAmplitudeIn_iff_tensorSingleConcentratedIn,
    tensorSingleConcentratedIn_iff_derivedTensor]
  -- tensoring the supported localization triangle with `κ_T`
  let Φ := (-⊗ᴸ-(T)[A]).flip.obj (constantSingle A T κ)
  let T' := supportedLocalizationTriangle A i j K (supportedLocalizationBoundary A i j hij K)
  have hT : Φ.mapTriangle.obj T' ∈ distTriang _ :=
    Φ.map_distinguished _ (supportedLocalizationTriangle_mem_distTriang A i j hij K)
  have h₂ : _root_.DerivedCategory.homologyConcentratedIn a b
      (((-⊗ᴸ-(T)[A]).obj K).obj (constantSingle A T κ)) :=
    hta ((constantSheaf T.smallEtaleTopology A).obj κ)
  have h₃ := homologyConcentratedIn_derivedTensor_rightDerivedLowerStar_constantSingle j hc K κ h₂
  have h₁ := homologyConcentratedIn_obj₁_of_distTriang _ hT (b' := b + c) (by lia) h₂ h₃
  -- `Ri_! Ri^! K ⊗ᴸ κ_T ≅ Ri_!(Ri^! K ⊗ᴸ κ_Z)`, by the projection formula for `Ri_!`
  let V := ((-⊗ᴸ-(Z)[A]).obj N).obj (constantSingle A Z κ)
  let eP : ((-⊗ᴸ-(T)[A]).obj ((R(i)_![A]).obj N)).obj (constantSingle A T κ) ≅
      (R(i)_![A]).obj V :=
    rightDerivedLowerShriekProjectionIso Λ i N _ ≪≫
      (R(i)_![A]).mapIso (((-⊗ᴸ-(Z)[A]).obj N).mapIso
        (leftDerivedUpperStarSingleConstantSheafIso A i κ))
  obtain ⟨h₁a, h₁b⟩ := h₁
  have : (((-⊗ᴸ-(T)[A]).obj ((R(i)_![A]).obj N)).obj (constantSingle A T κ)).IsGE a := h₁a
  have : (((-⊗ᴸ-(T)[A]).obj ((R(i)_![A]).obj N)).obj (constantSingle A T κ)).IsLE
      (b + c + 1) := h₁b
  have : ((R(i)_![A]).obj V).IsGE a := _root_.DerivedCategory.TStructure.t.isGE_of_iso eP a
  have : ((R(i)_![A]).obj V).IsLE (b + c + 1) :=
    _root_.DerivedCategory.TStructure.t.isLE_of_iso eP (b + c + 1)
  have : (D((i)^*[A]).obj ((R(i)_![A]).obj V)).IsGE a :=
    Functor.isGE_mapDerivedCategory_obj _ _ a
  have : (D((i)^*[A]).obj ((R(i)_![A]).obj V)).IsLE (b + c + 1) :=
    Functor.isLE_mapDerivedCategory_obj _ _ _
  exact ⟨_root_.DerivedCategory.TStructure.t.isGE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i V) a,
    _root_.DerivedCategory.TStructure.t.isLE_of_iso
      (mapDerivedUpperStarRightDerivedLowerShriekIso i V) (b + c + 1)⟩
include hij in
/-- Blueprint `prop-exc-closed-tor`: Finite Tor amplitude for closed support.

Let `Λ` be a finite ring (in the blueprint `Λ = 𝒪_E / ϖⁿ`), `i : Z ⟶ T` a closed immersion with
quasi-compact open complement `j : U ⟶ T`, such that `R^q j_*` vanishes on all sheaves of
`Λ`-modules for `q > c` and carries constructible sheaves to constructible sheaves
(`AlgebraicGeometry.Etale.OpenComplementCondition`). If `K` is bounded constructible with Tor
amplitude in `[a, b]`, then `Ri^! K` is bounded constructible with Tor amplitude in
`[a, b + c + 1]`.

Constructibility is `AlgebraicGeometry.Etale.constructibleIn_rightDerivedUpperShriek`
(`lem-exc-closed-amplitude`), `K` having homology in `[a, b]`; the Tor amplitude is
`AlgebraicGeometry.Etale.torAmplitudeIn_rightDerivedUpperShriek`. -/
theorem boundedConstructible_torAmplitudeIn_rightDerivedUpperShriek {c : ℕ}
    (h : OpenComplementCondition Λ j c) {a b : ℤ}
    {K : _root_.DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) T K)
    (hta : torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K) :
    DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) Z
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) ∧
      torAmplitudeIn (ModuleCat.{u + 1} Λ) Z a (b + c + 1)
        ((R(i)^![ModuleCat.{u + 1} Λ]).obj K) :=
  ⟨(constructibleIn_rightDerivedUpperShriek i j hij h
      ⟨hK, _root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta⟩).1,
    torAmplitudeIn_rightDerivedUpperShriek i j hij h.1 hta⟩

end Etale

end AlgebraicGeometry
