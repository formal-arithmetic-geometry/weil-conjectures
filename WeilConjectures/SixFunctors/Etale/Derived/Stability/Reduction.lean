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

/-- The finite coefficient comparison for the exceptional inverse image.

For a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes, `L ∈ Dctf(Y, Λ)` and
`B = Λ ⧸ J`, there is an isomorphism `(Rf^! L) ⊗ᴸ B ≅ Rf_B^!(L ⊗ᴸ B)`, which after restriction of
scalars to `Λ` reads `(Rf^! L)_B ≅ Rf^!(L_B)`.

The isomorphism is the exceptional tensor map `Rf^! L ⊗ᴸ Lf^* N ⟶ Rf^!(L ⊗ᴸ N)` for the constant
sheaf `N = B` on `Y`, which is invertible by the exceptional Künneth formula applied to the
squares with identity sides over `Y` and over `Spec k`, composed with the identification
`Lf^* B ≅ B` of constant sheaves. No algebraic closedness of `k` is needed. -/
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
  have hK := isExceptionalKunneth Λ k f aY
  let sqP : IsPullback (𝟙 Y) aY aY (𝟙 (Spec (.of k))) := IsPullback.of_id_fst
  let sq : IsPullback (𝟙 X) f f (𝟙 Y) := IsPullback.of_id_fst
  have h := hK (W := Spec (.of k)) (P := Y) (Q := X) (q := 𝟙 Y) (r := aY)
    (q' := 𝟙 X) (h := f) aY (𝟙 _) sqP sq
  have hh := h.2 L
    (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) B)
  let : IsIso (rightDerivedUpperShriekTensorMap f
      ((L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).obj L)
      ((L((aY)^*[ModuleCat.{u + 1} Λ])).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) B))) := hh
  have := isIso_lowerShriekRightAdjointTensorMap_of_iso_left
    (rightDerivedUpperShriekAdjunction Λ f) (M := (L((𝟙 Y)^*[ModuleCat.{u + 1} Λ])).obj L)
      (M' := L) ((leftDerivedUpperStarId _ Y).app L)
    (N := (L((aY)^*[ModuleCat.{u + 1} Λ])).obj
      (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) B))
  have := isIso_lowerShriekRightAdjointTensorMap_of_iso_right
    (rightDerivedUpperShriekAdjunction Λ f) (M := L)
      (N := (L((aY)^*[ModuleCat.{u + 1} Λ])).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) B))
      (N' := N)
      (leftDerivedUpperStarSingleConstantSheafIso (ModuleCat.{u + 1} Λ) aY B)
  let t := rightDerivedUpperShriekTensorMap f L N
  let iT : IsIso t := by
    dsimp [t]
    infer_instance
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

Let `k` be algebraically closed, `Λ` a finite ring whose exponent is invertible on `k` (the
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
