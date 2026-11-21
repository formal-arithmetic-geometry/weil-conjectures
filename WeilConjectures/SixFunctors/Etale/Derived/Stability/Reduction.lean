/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DerivedHomConstantTensorIso
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekConstantTensor
public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Exceptional.Local

/-!
# Finite coefficient reduction on `Dctf`

Let `Λ` be a finite ring whose exponent is invertible on a field `k` (the finite stage
`A = A_{E,n}`) and `J` an ideal of `Λ`, so that `B = Λ ⧸ J` is a finite coefficient quotient. The
reduction `K ↦ K ⊗ᴸ (Λ/J)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`) is the coefficient change
`K ↦ K_B` read after restriction of scalars to `Λ`. This file shows that on constructible
complexes of finite Tor amplitude it commutes with the six operations at the finite stage.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_app`: the canonical map
  `(Rf_* K)_B ⟶ Rf_*(K_B)` is an
  isomorphism for `K ∈ Dctf`.
- `AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_reductionModIdeal`: the evaluation-defined map
  `RHom(K, M)_B ⟶ RHom(K, M_B)` is an isomorphism for `K, M ∈ Dctf`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_dualizingComplex`: `(ω_X)_B ≅ Ra_X^! B`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_verdierDual`:
  `(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedUpperShriek`: the
  coefficient comparison `(Rf^! L)_B ≅ Rf^!(L_B)`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_stability_reductionModIdeal`: coefficient
  reduction commutes with all six operations on finite-Tor constructible complexes.

## Implementation notes

The coefficient change `D(X, A) ⥤ D(X, B)` is not available as a functor for a non-flat
`A ⟶ B`, so every comparison is stated after restriction of scalars: `RHom_B(K_B, M_B)` restricts
to `RHom_A(K, M ⊗ᴸ B)`, `𝔻_{X,B}(K_B) = RHom_B(K_B, ω_{X,B})` to `RHom_A(K, Ra_X^! B)`, and
`Rf_B^!` commutes with restriction of scalars. The comparisons are not equipped here with
compatibility statements for evaluation, units, or counits.

The integral and rational comparisons use `AlgebraicGeometry.Etale.preservationMatrix_integral`
and the integral exceptional adjoint. The integral category
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral` has a uniform Tor bound on
the reductions, so `Dᵇc(X, 𝒪_E) = Dctf(X, 𝒪_E)` there.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (J : Ideal Λ) {k : Type u} [Field k]

/-- The reduction of a tensor product: `(K ⊗ᴸ M)_B ≅ K ⊗ᴸ M_B`, by associativity. -/
noncomputable def reductionModIdealDerivedTensorIso {X : Scheme.{u}}
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (reductionModIdeal Λ X J).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) ≅
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((reductionModIdeal Λ X J).obj M) :=
  derivedTensorAssociator _ X K M _

/-- Finite coefficient change for direct image.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes and `K` a bounded above complex. The
canonical
projection map `(Rf_* K) ⊗ᴸ (Λ/J)_Y ⟶ Rf_*(K ⊗ᴸ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdealMap`), that is
`(Rf_* K)_B ⟶ Rf_*(K_B)` read after restriction of scalars, is an isomorphism. It is natural in
`K` by construction.

`K` is bounded above, and the projection formula holds for `Rf_*` and a finitely generated
constant coefficient. -/
theorem isIso_rightDerivedLowerStarReductionModIdealMap_app {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) (b : ℤ)
    [K.IsLE b] :
    IsIso ((rightDerivedLowerStarReductionModIdealMap Λ J f).app K) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ aX aY f hf d hd K b
    (ModuleCat.of Λ (Λ ⧸ J))
  -- the second factor is built through `-⊗ᴸ-` so that its instances match those of the map
  change IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} Λ) f).app K).app
      (constantSingle (ModuleCat.{u + 1} Λ) Y (ModuleCat.of Λ (Λ ⧸ J))) ≫ _)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this ((R((f)_*[ModuleCat.{u + 1} Λ])).mapIso
    (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).mapIso
      (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f
        (ModuleCat.of Λ (Λ ⧸ J))))).isIso_hom

/-- Finite coefficient change for internal Hom.

Let `X` be of finite type over `k`, `Λ` a finite ring whose exponent is invertible on `X` and
`B = Λ ⧸ J`. For `K, M ∈ Dctf(X, Λ)` the evaluation-defined map
`RHom_Λ(K, M) ⊗ᴸ B ⟶ RHom_B(K_B, M_B)` is an isomorphism. Read after restriction of scalars to
`Λ`, where `RHom_B(K_B, M_B)` becomes `RHom_Λ(K, M ⊗ᴸ (Λ/J)_X)`, the map is the transpose of
`ev ⊗ (Λ/J)_X`. -/
theorem isIso_derivedHomTensorMap_reductionModIdeal {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    IsIso (derivedHomTensorMap K M
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)))) :=
  isIso_derivedHomTensorMap_constantSingle aX hK hM (ModuleCat.of Λ (Λ ⧸ J))

/-- The internal hom commutes with finite coefficient reduction in its second variable on
`Dctf`: `RHom(K, M)_B ≅ RHom(K, M_B)`. -/
theorem nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((reductionModIdeal Λ X J).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((reductionModIdeal Λ X J).obj M)) :=
  have := isIso_derivedHomTensorMap_reductionModIdeal Λ J aX hK hM
  ⟨@asIso _ _ _ _ _ this⟩

/-- Finite coefficient change for the dualizing object.

For `a_X : X ⟶ Spec k` separated of finite type and `B = Λ ⧸ J`, there is an isomorphism
`ω_{X,Λ} ⊗ᴸ B ≅ ω_{X,B}`. Read after restriction of scalars to `Λ`, under which
`ω_{X,B} = Ra_{X,B}^! B` becomes `Ra_X^! (B_k)`, it is
`(Ra_X^! Λ) ⊗ᴸ (Λ/J)_X ≅ Ra_X^! ((Λ/J)_k)`. -/
theorem nonempty_iso_reductionModIdeal_dualizingComplex [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [HasCompactification aX] :
    Nonempty ((reductionModIdeal Λ X J).obj (dualizingComplex Λ aX) ≅
      (R(aX)^![Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) (ModuleCat.of Λ (Λ ⧸ J)))) :=
  have := isIso_dualizingComplexTensorMap_constantSingle_of_field Λ aX (ModuleCat.of Λ (Λ ⧸ J))
  ⟨((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj (dualizingComplex Λ aX)).mapIso
      (leftDerivedUpperStarSingleConstantSheafIso _ aX _).symm ≪≫
    asIso (dualizingComplexTensorMap Λ aX _)⟩

omit [Finite Λ] in
/-- The unit `Λ_X` lies in `Dctf(X, Λ)`. -/
lemma constructibleFiniteTor_tensorUnit (X : Scheme.{u}) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  ⟨(boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

variable [HasInvertibleExponent Λ (Spec (.of k))]

/-- Finite coefficient change for Verdier duality.

For `X` separated of finite type over `k`, `K ∈ Dctf(X, Λ)` and `B = Λ ⧸ J`, there is an
isomorphism `(𝔻_{X,Λ} K) ⊗ᴸ B ≅ 𝔻_{X,B}(K_B)`; after restriction of scalars to `Λ`,
`(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`. It is obtained by applying the internal-hom comparison to the
dualizing complex and then the comparison for the dualizing object. -/
theorem nonempty_iso_reductionModIdeal_verdierDual {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((reductionModIdeal Λ X J).obj ((verdierDual Λ aX).obj (op K)) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((R(aX)^![Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) (ModuleCat.of Λ (Λ ⧸ J))))) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have hω := constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aX
    (constructibleFiniteTor_tensorUnit Λ _)
  obtain ⟨e₁⟩ := nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor Λ J aX hK hω
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_dualizingComplex Λ J aX
  exact ⟨e₁ ≪≫ (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso e₂⟩

set_option maxHeartbeats 800000 in
-- The affine factorization and localization descent expand the derived tensor comparison.
/-- The finite coefficient comparison for the exceptional inverse image.

For a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes, `L ∈ Dctf(Y, Λ)` and
`B = Λ ⧸ J`, there is an isomorphism `(Rf^! L) ⊗ᴸ B ≅ Rf_B^!(L ⊗ᴸ B)`, which after restriction of
scalars to `Λ` reads `(Rf^! L)_B ≅ Rf^!(L_B)`.

The isomorphism is the exceptional tensor map `Rf^! L ⊗ᴸ Lf^* N ⟶ Rf^!(L ⊗ᴸ N)` for the constant
sheaf `N = B` on `Y`. Its invertibility is checked locally on `X`: affine pieces factor through
an affine space, where the closed-immersion case follows from the localization triangle and
the direct-image coefficient comparison. No algebraic closedness of `k` is needed. -/
theorem nonempty_iso_reductionModIdeal_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) (_hf : f ≫ aY = aX) [HasCompactification f]
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (_hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((reductionModIdeal Λ X J).obj ((R(f)^![Λ]).obj L) ≅
      (R(f)^![Λ]).obj ((reductionModIdeal Λ Y J).obj L)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace aX
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let : QuasiCompact f := inferInstance
  let B := ModuleCat.of Λ (Λ ⧸ J)
  let N := constantSingle (ModuleCat.{u + 1} Λ) Y B
  have ht : IsIso (rightDerivedUpperShriekTensorMap f L N) := by
    have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (f ≫ aY)
    have : IsNoetherian X := { __ := LocallyOfFiniteType.isLocallyNoetherian (f ≫ aY) }
    have hx (x : X) : ∃ (V : Y.Opens) (U : X.Opens), IsAffineOpen V ∧ IsAffineOpen U ∧
        x ∈ U ∧ U ≤ f ⁻¹ᵁ V := by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
      obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (f ⁻¹ᵁ V : Set X) from hxV) (f ⁻¹ᵁ V).isOpen
      exact ⟨V, U, hV, hU, hxU, hUV⟩
    choose V U hV hU hxU hUV using hx
    refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ
      (fun x ↦ (U x).ι) (fun x ↦ ⟨x, ⟨x, hxU x⟩, by simp⟩) _ fun x ↦ ?_
    have : IsAffine (U x) := hU x
    have : IsAffine (V x) := hV x
    let u := (U x).ι
    let v := (V x).ι
    let g := f.resLE (V x) (U x) (hUV x)
    have : HasCompactification v := (Compactification.ofIsOpenImmersion _).hasCompactification
    have : HasCompactification u := (Compactification.ofIsOpenImmersion _).hasCompactification
    have : HasCompactification (u ≫ f) :=
      ((HasCompactification.compactification f).precomp u).hasCompactification
    have : HasCompactification g := HasCompactification.of_isQuasiAffine _
    have : HasInvertibleExponent Λ Y := .of_hom aY
    have hMv := constructibleFiniteTor_rightDerivedUpperShriek Λ aY v _hL
    let Mv := (R(v)^![Λ]).obj L
    have hAffine : IsIso (rightDerivedUpperShriekTensorMap g Mv
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N)) := by
      obtain ⟨s, _, c, hc, hcf⟩ := exists_isClosedImmersion_affineSpace g
      let p := (𝔸(s; V x) ↘ V x)
      have hcp : c ≫ p = g := hcf
      have : HasCompactification c := .of_isProper _
      have : HasCompactification p := inferInstance
      have : HasInvertibleExponent Λ (𝔸(s; V x)) := .of_hom (p ≫ v ≫ aY)
      have : HasInvertibleExponent Λ (V x) := .of_hom (v ≫ aY)
      have hMcp := constructibleFiniteTor_rightDerivedUpperShriek Λ (v ≫ aY) p hMv
      obtain ⟨a, b, hab⟩ :=
        (DerivedCategory.exists_constructibleTorAmplitudeIn_iff_constructibleFiniteTor _).2 hMcp
      let Mc := (R(p)^![Λ]).obj Mv
      have : Mc.IsLE b := hab.1.2.2
      have := isIso_projectionMap_of_finite Λ c
      have hc' : IsIso (rightDerivedUpperShriekTensorMap c Mc
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj
            ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N))) := by
        have hclosed := isIso_rightDerivedUpperShriekTensorMap_constantSingle_of_isClosedImmersion
          Λ (p ≫ v ≫ aY) c Mc b B
        exact isIso_lowerShriekRightAdjointTensorMap_of_iso_right
          (rightDerivedUpperShriekAdjunction Λ c)
          ((leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) p B).symm ≪≫
            (L((p)^*[ModuleCat.{u + 1} Λ])).mapIso
              (leftDerivedUpperStarSingleConstantSheafIso
                (ModuleCat.{u + 1} Λ) v B).symm)
      have hp' : IsIso (rightDerivedUpperShriekTensorMap p Mv
          ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N)) := by
        have hθ := isIso_dualizingComplexTensorMapOfIsIso_of_smoothOfRelativeDimension Λ p
          (Nat.card s)
        exact isIso_lowerShriekRightAdjointTensorMap_of_forall
          (rightDerivedUpperShriekAdjunction Λ p) (projectionMapAssociativity Λ p) hθ Mv _
      obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
      let adjc := rightDerivedUpperShriekAdjunction Λ c
      let adjp := rightDerivedUpperShriekAdjunction Λ p
      let adjg := rightDerivedUpperShriekAdjunction Λ g
      let ρ : R(g)^![Λ] ≅ R(p)^![Λ] ⋙ R(c)^![Λ] := {
        hom := conjugateEquiv (adjg.ofNatIsoLeft (E c p g hcp)) (adjc.comp adjp) (𝟙 _)
        inv := conjugateEquiv (adjc.comp adjp) (adjg.ofNatIsoLeft (E c p g hcp)) (𝟙 _)
        hom_inv_id := conjugateEquiv_comm _ _ (by simp)
        inv_hom_id := conjugateEquiv_comm _ _ (by simp) }
      have hρ : ∀ K, (R(p)_![ModuleCat.{u + 1} Λ]).map
          ((R(c)_![ModuleCat.{u + 1} Λ]).map (ρ.hom.app K)) ≫
          (R(p)_![ModuleCat.{u + 1} Λ]).map (adjc.counit.app _) ≫ adjp.counit.app K =
          (E c p g hcp).inv.app _ ≫ adjg.counit.app K := by
        intro K
        have h := conjugateEquiv_counit (adjg.ofNatIsoLeft (E c p g hcp))
          (adjc.comp adjp) (𝟙 _) K
        simpa [ρ, adjc, adjp, adjg] using h
      have hc := Adjunction.projectionTensorMap_comp adjc adjp adjg
        (πf := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) c).app M).app N)
        (πh := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
        (πg := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) p).app M).app N)
        (projectionMap_app_app_naturality_left c)
        (projectionMap_app_app_naturality_left p)
        (fun N ↦ (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) c p g hcp.symm).hom.app N)
        (E c p g hcp) (hPF c p g hcp).comp ρ.hom hρ Mv
        ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N)
      have hiso : IsIso (rightDerivedUpperShriekTensorMap g Mv
          ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
            ρ.hom.app (Mv ⊗ ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N))) := by
        rw [hc]
        infer_instance
      let := hiso
      exact IsIso.of_isIso_comp_right _
        (ρ.hom.app (Mv ⊗ ((L((v)^*[ModuleCat.{u + 1} Λ])).obj N)))
    have hgv : g ≫ v = u ≫ f := by rw [Scheme.Hom.resLE_comp_ι]
    have hN_v : IsIso (rightDerivedUpperShriekTensorMap v L N) := by
      have hθv := isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ v
      exact isIso_lowerShriekRightAdjointTensorMap_of_forall
        (rightDerivedUpperShriekAdjunction Λ v) (projectionMapAssociativity Λ v) hθv L N
    obtain ⟨E, hPF, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
    have hcomp : IsIso (rightDerivedUpperShriekTensorMap (u ≫ f) L N) := by
      let adjg := rightDerivedUpperShriekAdjunction Λ g
      let adjv := rightDerivedUpperShriekAdjunction Λ v
      let adjh := rightDerivedUpperShriekAdjunction Λ (u ≫ f)
      let ρ : R(u ≫ f)^![Λ] ≅ R(v)^![Λ] ⋙ R(g)^![Λ] := {
        hom := conjugateEquiv (adjh.ofNatIsoLeft (E g v _ hgv)) (adjg.comp adjv) (𝟙 _)
        inv := conjugateEquiv (adjg.comp adjv) (adjh.ofNatIsoLeft (E g v _ hgv)) (𝟙 _)
        hom_inv_id := conjugateEquiv_comm _ _ (by simp)
        inv_hom_id := conjugateEquiv_comm _ _ (by simp) }
      have hρ : ∀ K, (R(v)_![ModuleCat.{u + 1} Λ]).map
          ((R(g)_![ModuleCat.{u + 1} Λ]).map (ρ.hom.app K)) ≫
          (R(v)_![ModuleCat.{u + 1} Λ]).map (adjg.counit.app _) ≫ adjv.counit.app K =
          (E g v _ hgv).inv.app _ ≫ adjh.counit.app K := by
        intro K
        have h := conjugateEquiv_counit (adjh.ofNatIsoLeft (E g v _ hgv))
          (adjg.comp adjv) (𝟙 _) K
        simpa [ρ, adjg, adjv, adjh] using h
      have hc := Adjunction.projectionTensorMap_comp adjg adjv adjh
        (πf := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) g).app M).app N)
        (πh := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) (u ≫ f)).app M).app N)
        (πg := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) v).app M).app N)
        (projectionMap_app_app_naturality_left g)
        (projectionMap_app_app_naturality_left v)
        (fun N ↦ (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) g v (u ≫ f) hgv.symm).hom.app N)
        (E g v _ hgv) (hPF g v _ hgv).comp ρ.hom hρ L N
      have hiso : IsIso (rightDerivedUpperShriekTensorMap (u ≫ f) L N ≫
          ρ.hom.app (L ⊗ N)) := by
        rw [hc]
        infer_instance
      let := hiso
      exact IsIso.of_isIso_comp_right (rightDerivedUpperShriekTensorMap (u ≫ f) L N)
        (ρ.hom.app (L ⊗ N))
    have hθu := isIso_dualizingComplexTensorMap_of_isOpenImmersion Λ u
    obtain ⟨Euf, hPFuf, -⟩ := exists_rightDerivedLowerShriekCompIso Λ
    let adju := rightDerivedUpperShriekAdjunction Λ u
    let adjf := rightDerivedUpperShriekAdjunction Λ f
    let adjuf := rightDerivedUpperShriekAdjunction Λ (u ≫ f)
    let ρuf : R(u ≫ f)^![Λ] ≅ R(f)^![Λ] ⋙ R(u)^![Λ] := {
      hom := conjugateEquiv (adjuf.ofNatIsoLeft (Euf u f _ rfl)) (adju.comp adjf) (𝟙 _)
      inv := conjugateEquiv (adju.comp adjf) (adjuf.ofNatIsoLeft (Euf u f _ rfl)) (𝟙 _)
      hom_inv_id := conjugateEquiv_comm _ _ (by simp)
      inv_hom_id := conjugateEquiv_comm _ _ (by simp) }
    have hρuf : ∀ K, (R(f)_![ModuleCat.{u + 1} Λ]).map
        ((R(u)_![ModuleCat.{u + 1} Λ]).map (ρuf.hom.app K)) ≫
        (R(f)_![ModuleCat.{u + 1} Λ]).map (adju.counit.app _) ≫ adjf.counit.app K =
        (Euf u f _ rfl).inv.app _ ≫ adjuf.counit.app K := by
      intro K
      have h := conjugateEquiv_counit (adjuf.ofNatIsoLeft (Euf u f _ rfl))
        (adju.comp adjf) (𝟙 _) K
      simpa [ρuf, adju, adjf, adjuf] using h
    have huf := Adjunction.projectionTensorMap_comp adju adjf adjuf
      (πf := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) u).app M).app N)
      (πh := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) (u ≫ f)).app M).app N)
      (πg := fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
      (projectionMap_app_app_naturality_left u)
      (projectionMap_app_app_naturality_left f)
      (fun N ↦ (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u f (u ≫ f) rfl).hom.app N)
      (Euf u f _ rfl) (hPFuf u f _ rfl).comp ρuf.hom hρuf L N
    have huf' : IsIso (rightDerivedUpperShriekTensorMap (u ≫ f) L N ≫
        ρuf.hom.app (L ⊗ N)) := by
      let := hcomp
      infer_instance
    let := huf'
    have hunit := isIso_lowerShriekRightAdjointTensorMap_of_forall adju
      (projectionMapAssociativity Λ u) hθu (R(f)^![Λ].obj L)
      ((L((f)^*[ModuleCat.{u + 1} Λ])).obj N)
    let := hunit
    have hmap : IsIso ((R(u)^![Λ]).map
        (rightDerivedUpperShriekTensorMap f L N)) := by
      rw [huf] at huf'
      have := (isIso_comp_left_iff _ _).1 huf'
      have hmid : IsIso ((R(u)^![Λ].obj (R(f)^![Λ].obj L) ◁
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u f (u ≫ f) rfl).hom.app N) ≫
        adju.projectionTensorMap
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) u).app M).app N)
          (R(f)^![Λ].obj L) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
        (R(u)^![Λ]).map (lowerShriekRightAdjointTensorMap adjf L N)) := by
        simpa [rightDerivedUpperShriekTensorMap, adju, adjf] using this
      change IsIso ((R(u)^![Λ]).map
        (lowerShriekRightAdjointTensorMap adjf L N))
      have hmid' : IsIso ((R(u)^![Λ].obj (R(f)^![Λ].obj L) ◁
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u f (u ≫ f) rfl).hom.app N) ≫
        (adju.projectionTensorMap
          (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) u).app M).app N)
          (R(f)^![Λ].obj L) ((L((f)^*[ModuleCat.{u + 1} Λ])).obj N) ≫
          (R(u)^![Λ]).map (lowerShriekRightAdjointTensorMap adjf L N))) := by
        simpa [Category.assoc] using hmid
      have hmid'' := (isIso_comp_left_iff
        (R(u)^![Λ].obj (R(f)^![Λ].obj L) ◁
          (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) u f (u ≫ f) rfl).hom.app N)
        _).1 hmid'
      exact (isIso_comp_left_iff _ _).1 hmid''
    exact isIso_leftDerivedUpperStar_map_of_isIso_rightAdjoint_map
      adju hθu
      (isInvertible_dualizingComplex_of_etale Λ u) _
      (by simpa [rightDerivedUpperShriekTensorMap] using hmap)
  let t := rightDerivedUpperShriekTensorMap f L N
  let iT : IsIso t := by
    dsimp [t]
    exact ht
  let e := leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) f B
  let m := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
    ((R(f)^![Λ]).obj L)).map e.inv
  let iM : IsIso m := by
    dsimp [m]
    infer_instance
  exact ⟨@asIso _ _ _ _ m iM ≪≫ @asIso _ _ _ _ t iT⟩

variable [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- Coefficient reduction commutes with the six operations at the finite stage.

Let `k` be a field, `Λ` a finite ring whose exponent is invertible on `k` (the
finite stage `A = A_{E,n}`), `B = Λ ⧸ J` a finite coefficient quotient and `f : X ⟶ Y` a morphism
of separated finite-type `k`-schemes. On the finite-Tor constructible domains, the coefficient
reduction `K ↦ K_B = K ⊗ᴸ (Λ/J)_X` (read after restriction of scalars to `Λ`) commutes with
pullback, tensor product, both direct images, general internal Hom, Verdier duality and the
exceptional inverse image:

1. `(Lf^* K)_B ≅ Lf^*(K_B)`;
2. `(K ⊗ᴸ M)_B ≅ K ⊗ᴸ M_B`, the restriction of `K_B ⊗ᴸ_B M_B`;
3. `(Rf_* K)_B ≅ Rf_*(K_B)` for `K ∈ Dctf`;
4. `(Rf_! K)_B ≅ Rf_!(K_B)`;
5. `RHom(K, M)_B ≅ RHom(K, M_B)`, the restriction of `RHom_B(K_B, M_B)`, for `K, M ∈ Dctf`.
6. `(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`, the restriction of `𝔻_{X,B}(K_B)`, for `K ∈ Dctf`.
7. `(Rf^! L)_B ≅ Rf^!(L_B)` for `L ∈ Dctf`.

The compatibility of these comparisons with evaluation and adjunction maps is not recorded. For
the integral and rational stages of clause (vii) see the module documentation. -/
theorem constructibleFiniteTor_stability_reductionModIdeal {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f] :
    (∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty ((reductionModIdeal Λ X J).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ≅
        (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ Y J).obj K))) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty ((reductionModIdeal Λ X J).obj (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj M) ≅
        ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj K).obj ((reductionModIdeal Λ X J).obj M))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        Nonempty ((reductionModIdeal Λ Y J).obj ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) ≅
          (R((f)_*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ X J).obj K))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      Nonempty ((reductionModIdeal Λ Y J).obj ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) ≅
        (R(f)_![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ X J).obj K))) ∧
    (∀ K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M →
          Nonempty ((reductionModIdeal Λ X J).obj
              ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) ≅
            (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((reductionModIdeal Λ X J).obj M))) ∧
    (∀ K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K →
        Nonempty ((reductionModIdeal Λ X J).obj
            ((verdierDual Λ aX).obj (op K)) ≅
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((R(aX)^![Λ]).obj
            (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k))
              (ModuleCat.of Λ (Λ ⧸ J)))))) ∧
    (∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
        Nonempty ((reductionModIdeal Λ X J).obj ((R(f)^![Λ]).obj L) ≅
          (R(f)^![Λ]).obj ((reductionModIdeal Λ Y J).obj L))) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  obtain ⟨eS⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite Λ f J
  refine ⟨fun K ↦ ⟨((leftDerivedUpperStarReductionModIdealIso Λ J f).app K).symm⟩,
    fun K M ↦ ⟨reductionModIdealDerivedTensorIso Λ J K M⟩,
    fun K hK ↦ by
      obtain ⟨-, a, b, hta⟩ := hK
      have : K.IsLE b := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta).2
      have := isIso_rightDerivedLowerStarReductionModIdealMap_app Λ J aX aY f hf K b
      exact ⟨@asIso _ _ _ _ _ this⟩,
    fun K ↦ ⟨eS.app K⟩,
    fun K M hK hM ↦
      nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor Λ J aX hK hM,
    fun K hK ↦ nonempty_iso_reductionModIdeal_verdierDual Λ J aX hK,
    fun L hL ↦ nonempty_iso_reductionModIdeal_rightDerivedUpperShriek Λ J aX aY f hf hL⟩

/-- Finite exceptional adjoints and coefficient change.

For a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes, `k` algebraically closed, and
`L ∈ Dctf(Y, Λ)` at a finite stage `Λ`:

1. `Rf^! L ≅ 𝔻_X Lf^* 𝔻_Y L`, the exceptional inverse image expressed through Verdier duality;
2. for a quotient `B = Λ ⧸ J`, `(Rf^! L) ⊗ᴸ B ≅ Rf_B^!(L ⊗ᴸ B)`, read after restriction of scalars
   to `Λ` as `(Rf^! L)_B ≅ Rf^!(L_B)`
   (`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedUpperShriek`).

The cocycle condition of the comparisons and their compatibility with units and counits are not
recorded. -/
theorem nonempty_iso_rightDerivedUpperShriek_verdierDual_and_reductionModIdeal {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((R(f)^![Λ]).obj L ≅
      (verdierDual Λ aX).obj
        (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj
          ((verdierDual Λ aY).obj (op L))))) ∧
    Nonempty ((reductionModIdeal Λ X J).obj ((R(f)^![Λ]).obj L) ≅
      (R(f)^![Λ]).obj ((reductionModIdeal Λ Y J).obj L)) :=
  ⟨nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hL,
    nonempty_iso_reductionModIdeal_rightDerivedUpperShriek Λ J aX aY f hf hL⟩

end Etale

end AlgebraicGeometry
