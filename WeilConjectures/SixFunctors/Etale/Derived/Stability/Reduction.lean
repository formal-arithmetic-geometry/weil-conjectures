/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Exchange
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.FiniteStage

/-!
# Finite coefficient reduction on `Dctf`

Let `Λ` be a finite ring whose exponent is invertible on a field `k` (the finite stage
`A = A_{E,n}`) and `J` an ideal of `Λ`, so that `B = Λ ⧸ J` is a finite coefficient quotient. The
reduction `K ↦ K ⊗ᴸ (Λ/J)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`) is the coefficient change
`K ↦ K_B` read after restriction of scalars to `Λ`. This file shows that on the constructible
complexes of finite Tor amplitude it commutes with the six operations: this is clause (vii) of
`thm-sf-ctf-stability` at the finite stage
(`AlgebraicGeometry.Etale.constructibleFiniteTor_stability_reductionModIdeal`).

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarReductionModIdealMap_app`
  (`lem-coef-finite-direct-image`): the canonical map `(Rf_* K)_B ⟶ Rf_*(K_B)` is an isomorphism
  for `K ∈ Dctf`.
- `AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_reductionModIdeal`
  (`thm-coef-finite-hom`): the evaluation-defined map `RHom(K, M)_B ⟶ RHom(K, M_B)` is an
  isomorphism for `K, M ∈ Dctf`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_dualizingComplex`
  (`lem-coef-finite-dualizing`): `(ω_X)_B ≅ Ra_X^! B`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_verdierDual`
  (`cor-coef-finite-verdier`): `(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`.
- `AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedUpperShriek`
  (`lem-coef-finite-exceptional`, the coefficient comparison): `(Rf^! L)_B ≅ Rf^!(L_B)`.
- `AlgebraicGeometry.Etale.constructibleFiniteTor_stability_reductionModIdeal`
  (`thm-sf-ctf-stability` (vii), finite stage).

## Implementation notes

The coefficient change `D(X, A) ⥤ D(X, B)` is not available as a functor for a non-flat
`A ⟶ B`, so every comparison is stated after restriction of scalars: `RHom_B(K_B, M_B)` restricts
to `RHom_A(K, M ⊗ᴸ B)`, `𝔻_{X,B}(K_B) = RHom_B(K_B, ω_{X,B})` to `RHom_A(K, Ra_X^! B)`, and
`Rf_B^!` commutes with restriction of scalars. The compatibilities of the comparisons with
evaluation, units and counits asserted by the blueprint are not recorded.

The integral and rational parts of clause (vii) are the results of the coefficient chapter:
`AlgebraicGeometry.Etale.preservationMatrix_integral` (`cor-coef-integral-internal-hom`,
`lem-coef-integral-hom-reduction`, `prop-coef-integral-exceptional-adjoint`); the integral category
`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructibleIntegral` is defined with a uniform
Tor bound on the reductions, so `Dᵇc(X, 𝒪_E) = Dctf(X, 𝒪_E)` holds by definition there.
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
  α_ K M (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)))

/-- Blueprint `lem-coef-finite-direct-image`: Finite coefficient change for direct image.

Let `f : X ⟶ Y` be a morphism of finite-type `k`-schemes and `K ∈ Dctf(X, Λ)`. The canonical
projection map `(Rf_* K) ⊗ᴸ (Λ/J)_Y ⟶ Rf_*(K ⊗ᴸ (Λ/J)_X)`
(`AlgebraicGeometry.Etale.rightDerivedLowerStarReductionModIdealMap`), that is
`(Rf_* K)_B ⟶ Rf_*(K_B)` read after restriction of scalars, is an isomorphism. It is natural in
`K` by construction.

`K` is bounded above, and the projection formula holds for `Rf_*` and a finitely generated
constant coefficient (`lem-sf-projection-finite-constant`,
`AlgebraicGeometry.Etale.isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle`). -/
theorem isIso_rightDerivedLowerStarReductionModIdealMap_app {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (f : X ⟶ Y) (hf : f ≫ aY = aX)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    IsIso ((rightDerivedLowerStarReductionModIdealMap Λ J f).app K) := by
  obtain ⟨-, a, b, hta⟩ := hK
  have : K.IsLE b := (_root_.DerivedCategory.homologyConcentratedIn_of_torAmplitudeIn hta).2
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_le aX
  have := isIso_rightDerivedLowerStarProjectionMap_app_app_constantSingle Λ aX aY f hf d hd K b
    (ModuleCat.of Λ (Λ ⧸ J))
  exact inferInstanceAs (IsIso (_ ≫ _))

/-- Blueprint `thm-coef-finite-hom`: Finite coefficient change for internal Hom.

Let `X` be of finite type over `k`, `Λ` a finite ring whose exponent is invertible on `X` and
`B = Λ ⧸ J`. For `K, M ∈ Dctf(X, Λ)` the evaluation-defined map
`RHom_Λ(K, M) ⊗ᴸ B ⟶ RHom_B(K_B, M_B)` is an isomorphism. Read after restriction of scalars to
`Λ`, where `RHom_B(K_B, M_B)` becomes `RHom_Λ(K, M ⊗ᴸ (Λ/J)_X)`, the map is the transpose of
`ev ⊗ (Λ/J)_X` (`AlgebraicGeometry.Etale.DerivedCategory.derivedHomTensorMap`). -/
theorem isIso_derivedHomTensorMap_reductionModIdeal {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    IsIso (derivedHomTensorMap K M
      (constantSingle (ModuleCat.{u + 1} Λ) X (ModuleCat.of Λ (Λ ⧸ J)))) :=
  sorry

/-- The internal hom commutes with finite coefficient reduction in its second variable on
`Dctf`: `RHom(K, M)_B ≅ RHom(K, M_B)`
(`AlgebraicGeometry.Etale.isIso_derivedHomTensorMap_reductionModIdeal`, `thm-coef-finite-hom`). -/
theorem nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor {X : Scheme.{u}}
    (aX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX] [HasInvertibleExponent Λ X]
    {K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X M) :
    Nonempty ((reductionModIdeal Λ X J).obj ((RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj M) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((reductionModIdeal Λ X J).obj M)) :=
  have := isIso_derivedHomTensorMap_reductionModIdeal Λ J aX hK hM
  ⟨asIso (derivedHomTensorMap K M _)⟩

/-- Blueprint `lem-coef-finite-dualizing`: Finite coefficient change for the dualizing object.

For `a_X : X ⟶ Spec k` separated of finite type and `B = Λ ⧸ J`, there is an isomorphism
`ω_{X,Λ} ⊗ᴸ B ≅ ω_{X,B}`. Read after restriction of scalars to `Λ`, under which
`ω_{X,B} = Ra_{X,B}^! B` becomes `Ra_X^! (B_k)`, it is
`(Ra_X^! Λ) ⊗ᴸ (Λ/J)_X ≅ Ra_X^! ((Λ/J)_k)`. -/
theorem nonempty_iso_reductionModIdeal_dualizingComplex [HasInvertibleExponent Λ (Spec (.of k))]
    {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [IsSeparated aX] [LocallyOfFiniteType aX]
    [QuasiCompact aX] [HasCompactification aX] :
    Nonempty ((reductionModIdeal Λ X J).obj (dualizingComplex (ModuleCat.{u + 1} Λ) aX) ≅
      (R(aX)^![ModuleCat.{u + 1} Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) (ModuleCat.of Λ (Λ ⧸ J)))) :=
  sorry

/-- The unit `Λ_X` lies in `Dctf(X, Λ)`. -/
lemma constructibleFiniteTor_tensorUnit (X : Scheme.{u}) :
    constructibleFiniteTor (ModuleCat.{u + 1} Λ) X (𝟙_ _) :=
  ⟨(boundedConstructible _ X).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (boundedConstructible_singleFunctor_obj _ 0), 0, 0,
    (torAmplitudeIn _ X 0 0).prop_of_iso (_root_.DerivedCategory.singleFunctorObjUnitIso _)
      (_root_.DerivedCategory.torAmplitudeIn_singleFunctor_obj_of_flat
        (ObjectProperty.flat_of_isDualizable isDualizable_unit))⟩

variable [HasInvertibleExponent Λ (Spec (.of k))]

/-- Blueprint `cor-coef-finite-verdier`: Finite coefficient change for Verdier duality, the
comparison isomorphism.

For `X` separated of finite type over `k`, `K ∈ Dctf(X, Λ)` and `B = Λ ⧸ J`, there is an
isomorphism `(𝔻_{X,Λ} K) ⊗ᴸ B ≅ 𝔻_{X,B}(K_B)`; after restriction of scalars to `Λ`,
`(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`. As in the blueprint, it is `thm-coef-finite-hom` with second
argument `ω_X` followed by `lem-coef-finite-dualizing`. -/
theorem nonempty_iso_reductionModIdeal_verdierDual {X : Scheme.{u}} (aX : X ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K) :
    Nonempty ((reductionModIdeal Λ X J).obj ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ≅
      (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((R(aX)^![ModuleCat.{u + 1} Λ]).obj
        (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) (ModuleCat.of Λ (Λ ⧸ J))))) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have hω := constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aX
    (constructibleFiniteTor_tensorUnit Λ _)
  obtain ⟨e₁⟩ := nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor Λ J aX hK hω
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_dualizingComplex Λ J aX
  exact ⟨e₁ ≪≫ (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).mapIso e₂⟩

variable [IsAlgClosed k]

/-- Blueprint `lem-coef-finite-exceptional`: the finite coefficient comparison for the exceptional
inverse image.

For a morphism `f : X ⟶ Y` of separated finite-type `k`-schemes, `L ∈ Dctf(Y, Λ)` and
`B = Λ ⧸ J`, there is an isomorphism `(Rf^! L) ⊗ᴸ B ≅ Rf_B^!(L ⊗ᴸ B)`, which after restriction of
scalars to `Λ` reads `(Rf^! L)_B ≅ Rf^!(L_B)`.

As in the blueprint, `Rf^! L ≅ 𝔻_X Lf^* 𝔻_Y L` (`thm-sf-ctf-stability` (v)), and the duality
comparisons (`cor-coef-finite-verdier`) move the reduction through both duals:
`(𝔻_X Lf^* 𝔻_Y L)_B ≅ RHom(Lf^* 𝔻_Y L, Ra_X^! B) ≅ RHom(Lf^* 𝔻_Y L, Rf^! Ra_Y^! B)
≅ Rf^! RHom(𝔻_Y L, Ra_Y^! B) ≅ Rf^! (𝔻_Y 𝔻_Y L)_B ≅ Rf^!(L_B)`, the middle step being duality
against pullback (`cor-sf-duality-pullback`). -/
theorem nonempty_iso_reductionModIdeal_rightDerivedUpperShriek {X Y : Scheme.{u}}
    (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [HasCompactification f]
    {L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L) :
    Nonempty ((reductionModIdeal Λ X J).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ≅
      (R(f)^![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ Y J).obj L)) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  have : HasInvertibleExponent Λ Y := .of_hom aY
  let N := constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k)) (ModuleCat.of Λ (Λ ⧸ J))
  let DL := (verdierDual (ModuleCat.{u + 1} Λ) aY).obj (op L)
  have hDL := constructibleFiniteTor_verdierDual Λ aY hL
  have hP := constructibleFiniteTor_leftDerivedUpperStar _ f hDL
  have hω := constructibleFiniteTor_dualizingComplex Λ (𝟙 _) aY
    (constructibleFiniteTor_tensorUnit Λ _)
  obtain ⟨e₁⟩ :=
    nonempty_iso_rightDerivedUpperShriek_verdierDual_leftDerivedUpperStar Λ aX aY f hf hL
  obtain ⟨e₂⟩ := nonempty_iso_reductionModIdeal_verdierDual Λ J aX hP
  subst hf
  have : QuasiCompact (f ≫ aY) := inferInstance
  obtain ⟨c⟩ := nonempty_iso_rightDerivedUpperShriek_comp Λ f aY
  obtain ⟨d⟩ := nonempty_rightDerivedUpperShriek_derivedHom_iso_of_finite Λ f
  obtain ⟨e₃⟩ := nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor Λ J aY hDL hω
  obtain ⟨e₄⟩ := nonempty_iso_reductionModIdeal_dualizingComplex Λ J aY
  obtain ⟨b⟩ := nonempty_iso_verdierDual_verdierDual Λ aY hL
  exact ⟨(reductionModIdeal Λ X J).mapIso e₁ ≪≫ e₂ ≪≫
    (RHom(X)[ModuleCat.{u + 1} Λ].obj (op ((L((f)^*[ModuleCat.{u + 1} Λ])).obj DL))).mapIso
      (c.app N) ≪≫ ((d.app (op DL)).app ((R(aY)^![ModuleCat.{u + 1} Λ]).obj N)).symm ≪≫
    (R(f)^![ModuleCat.{u + 1} Λ]).mapIso
      ((RHom(Y)[ModuleCat.{u + 1} Λ].obj (op DL)).mapIso e₄.symm ≪≫ e₃.symm ≪≫
        (reductionModIdeal Λ Y J).mapIso b.symm)⟩

/-- Blueprint `thm-sf-ctf-stability`, clause (vii), at the finite stage.

Let `k` be algebraically closed, `Λ` a finite ring whose exponent is invertible on `k` (the
finite stage `A = A_{E,n}`), `B = Λ ⧸ J` a finite coefficient quotient and `f : X ⟶ Y` a morphism
of separated finite-type `k`-schemes. On the finite-Tor constructible domains, the coefficient
reduction `K ↦ K_B = K ⊗ᴸ (Λ/J)_X` (read after restriction of scalars to `Λ`) commutes with
pullback, tensor product, both direct images, general internal Hom, Verdier duality and the
exceptional inverse image:

1. `(Lf^* K)_B ≅ Lf^*(K_B)` (`lem-fix-operation-reduction`);
2. `(K ⊗ᴸ M)_B ≅ K ⊗ᴸ M_B`, the restriction of `K_B ⊗ᴸ_B M_B`;
3. `(Rf_* K)_B ≅ Rf_*(K_B)` for `K ∈ Dctf` (`lem-coef-finite-direct-image`);
4. `(Rf_! K)_B ≅ Rf_!(K_B)` (`lem-fix-operation-reduction`);
5. `RHom(K, M)_B ≅ RHom(K, M_B)`, the restriction of `RHom_B(K_B, M_B)`, for `K, M ∈ Dctf`
   (`thm-coef-finite-hom`);
6. `(𝔻_X K)_B ≅ RHom(K, Ra_X^! B)`, the restriction of `𝔻_{X,B}(K_B)`, for `K ∈ Dctf`
   (`cor-coef-finite-verdier`);
7. `(Rf^! L)_B ≅ Rf^!(L_B)` for `L ∈ Dctf` (`lem-coef-finite-exceptional`).

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
            ((verdierDual (ModuleCat.{u + 1} Λ) aX).obj (op K)) ≅
          (RHom(X)[ModuleCat.{u + 1} Λ].obj (op K)).obj ((R(aX)^![ModuleCat.{u + 1} Λ]).obj
            (constantSingle (ModuleCat.{u + 1} Λ) (Spec (.of k))
              (ModuleCat.of Λ (Λ ⧸ J)))))) ∧
    (∀ L : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y L →
        Nonempty ((reductionModIdeal Λ X J).obj ((R(f)^![ModuleCat.{u + 1} Λ]).obj L) ≅
          (R(f)^![ModuleCat.{u + 1} Λ]).obj ((reductionModIdeal Λ Y J).obj L))) := by
  have : HasInvertibleExponent Λ X := .of_hom aX
  obtain ⟨eS⟩ := nonempty_iso_reductionModIdeal_rightDerivedLowerShriek_of_finite Λ f J
  refine ⟨fun K ↦ ⟨((leftDerivedUpperStarReductionModIdealIso Λ J f).app K).symm⟩,
    fun K M ↦ ⟨reductionModIdealDerivedTensorIso Λ J K M⟩,
    fun K hK ↦
      have := isIso_rightDerivedLowerStarReductionModIdealMap_app Λ J aX aY f hf hK
      ⟨asIso ((rightDerivedLowerStarReductionModIdealMap Λ J f).app K)⟩,
    fun K ↦ ⟨eS.app K⟩,
    fun K M hK hM ↦
      nonempty_iso_reductionModIdeal_derivedHom_of_constructibleFiniteTor Λ J aX hK hM,
    fun K hK ↦ nonempty_iso_reductionModIdeal_verdierDual Λ J aX hK,
    fun L hL ↦ nonempty_iso_reductionModIdeal_rightDerivedUpperShriek Λ J aX aY f hf hL⟩

end Etale

end AlgebraicGeometry
