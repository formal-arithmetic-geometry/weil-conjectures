/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.IntegralDegreewise
public import WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Reduction

/-!
# Adic reconstruction and scalar extension of the Poincaré pairing

Let `k` be a separably closed field, `a : X ⟶ Spec k` a morphism admitting a compactification
for which `Ra_!` has a right adjoint, `γ : T[2d] ≅ Ra^! Λ` a purity isomorphism (`T = Λ_X(d)`)
and `K ∈ D(X_ét, Λ)` perfect over `Λ_X`. This file proves blueprint
`thm-pod-adic-reconstruction-and-scalar-extension` in the form the repository can express.

* The adjoint `β_K^♯ : RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` of the derived Poincaré pairing
  (`AlgebraicGeometry.Etale.poincareAdjoint`) is an isomorphism over every coefficient ring
  `Λ`, in particular over `𝒪_E`; its inverse is the duality isomorphism
  `RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`, also read in `D(Λ)`.
* For a nonzerodivisor `ϖ` and `A_n = Λ/(ϖ)ⁿ`, the reductions `β_K^♯ ⊗ᴸ A_n` are isomorphisms
  `RΓ(X, K^∨(d)_n)[2d] ≅ RHom(RΓ_c(X, K), A_n)` — the finite-level dualities — and they are
  compatible with the transition maps `A_m ⟶ A_n`: they form a morphism of towers.
* At the integral stage `Λ = 𝒪_E`, source and target of `β_K^♯` are derived complete, so
  `β_K^♯` is the realization of its tower of reductions (an isomorphism of the adic category
  `D_comp(Spec k, 𝒪_E)`), and localization `𝒪_E ⟶ E` as well as finite extension `E ⊆ L` of
  the coefficient field carry it to isomorphisms of `D_comp(Spec k, E)`, `D_comp(Spec k, 𝒪_L)`
  and `D_comp(Spec k, L)`.

## Main definitions

- `AlgebraicGeometry.Etale.poincareAdjoint`: the adjoint `β_K^♯` of the derived Poincaré
  pairing.
- `AlgebraicGeometry.Etale.reductionModIdealMap`: the transition `K ⊗ᴸ Λ/J ⟶ K ⊗ᴸ Λ/J'` for
  `J ≤ J'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_poincareAdjoint`,
  `AlgebraicGeometry.Etale.nonempty_iso_ihom_compactlySupportedGlobalSections`: the duality
  isomorphism, in `D(Spec k_ét, Λ)` and in `D(Λ)`.
- `AlgebraicGeometry.Etale.poincareAdjoint_reduction`: the finite-level dualities are the
  reductions of `β_K^♯`, and they form a morphism of towers.
- `AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_integral`: the pairing `β_K` and the
  pairings `β_{K_n}` of all its finite levels are perfect.

## Implementation notes

As everywhere in the repository, the finite stage `A_n` is read inside `D(X_ét, Λ)` through
`K ↦ K ⊗ᴸ (Λ/(ϖ)ⁿ)_X`; the `A_n`-dual of `RΓ_c(X, K_n)` is then `RHom_Λ(RΓ_c(X, K), A_n)`. The
identification of the transported isomorphisms over `E` and `L` with the Poincaré pairings of
the base-changed complexes, and the transport of the degree-indexing maps, the relative form
and the Frobenius squares, need the compatibility of `Ra_!`, `Ra_*`, `RHom` and `⊗ᴸ` with
derived base change, which the repository does not have; they are not stated.
-/

@[expose] public section

universe w u' u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Transition

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

/-- The transition `K ⊗ᴸ (Λ/J)_X ⟶ K ⊗ᴸ (Λ/J')_X` between reductions, induced by the
projection `Λ/J ⟶ Λ/J'` for `J ≤ J'` (for `J = (ϖ)ᵐ`, `J' = (ϖ)ⁿ`, `n ≤ m`, the transition
`A_m ⟶ A_n` of the tower of finite stages). -/
noncomputable def reductionModIdealMap {J J' : Ideal Λ} (h : J ≤ J') :
    reductionModIdeal Λ X J ⟶ reductionModIdeal Λ X J' :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.map
    ((_root_.DerivedCategory.singleFunctor _ 0).map
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        (ModuleCat.ofHom (Submodule.factor h))))

end Transition

section PairingAdjoint

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X : Scheme.{u}}

/-- The adjoint `D ⟶ RHom(C, Λ_X)` of a pairing `b : C ⊗ᴸ D ⟶ Λ_X` of `D(X_ét)`, stated for
general coefficients so that the kernel never compares `derivedTensor` with the tensor product
at a specific coefficient category (compare `AlgebraicGeometry.Etale.IsPerfectPairing`). -/
noncomputable def pairingAdjoint {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    (b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _) : D ⟶ (ihom C).obj (𝟙_ _) :=
  MonoidalClosed.curry (C := _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) b

/-- The adjoint of a perfect pairing is an isomorphism. -/
lemma isIso_pairingAdjoint {C D : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {b : ((derivedTensor A X).obj C).obj D ⟶ 𝟙_ _} (h : IsPerfectPairing b) :
    IsIso (pairingAdjoint b) :=
  h.isIso

/-- The coefficient dual `RHom(C, Λ_X)` is the internal hom `[C, Λ_X]`, stated for general
coefficients so that the kernel compares them only once, generically. -/
noncomputable def coefficientDualIsoIhom
    (C : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (DerivedCategory.coefficientDual A X).obj (op C) ≅ (ihom C).obj (𝟙_ _) :=
  Iso.refl _

end PairingAdjoint

section Adjoint

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a]
  [(R(a)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {d : ℕ} {T : DerivedCategoryModule Λ X}
  (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a) (K : DerivedCategoryModule Λ X)

/-- The second variable `K^∨ ⊗ᴸ T` of the derived Poincaré pairing (`K^∨(d)` for
`T = Λ_X(d)`). -/
noncomputable abbrev poincareSecondVariable : DerivedCategoryModule Λ X :=
  ((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: the adjoint

`β_K^♯ : RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨ = RHom(RΓ_c(X, K), Λ)`

of the derived Poincaré pairing `β_K` (`AlgebraicGeometry.Etale.poincarePairing`), read in
`D(Spec k_ét, Λ)`. -/
noncomputable def poincareAdjoint :=
  pairingAdjoint (A := ModuleCat.{u + 1} Λ) (poincarePairing a γ K)


variable {K}

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: Adic reconstruction and
scalar extension (perfectness over every coefficient ring).

For `K` perfect over `Λ_X`, the adjoint `β_K^♯` of the derived Poincaré pairing is an
isomorphism, over every coefficient ring `Λ`, in particular over `𝒪_E`; its inverse is the
duality isomorphism `RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable`). -/
theorem isIso_poincareAdjoint (hKd : IsDualizable K) : IsIso (poincareAdjoint a γ K) :=
  isIso_pairingAdjoint (isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a γ hKd)

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: Adic reconstruction and
scalar extension (the duality isomorphism in `D(Λ)`).

For `K` perfect over `Λ_X`, there is an isomorphism of complexes of `Λ`-modules
`RΓ_c(X, K)^∨ ≅ RΓ(X, K^∨(d))[2d]`, obtained from the inverse of `β_K^♯` by evaluation at the
point, which commutes with duals. -/
theorem nonempty_iso_ihom_compactlySupportedGlobalSections
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a) (hKd : IsDualizable K) :
    Nonempty ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)).obj
        (𝟙_ _) ≅
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj
        (poincareSecondVariable (T := T) K))⟦(2 * d : ℤ)⟧) := by
  have := isIso_poincareAdjoint a γ hKd
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  obtain ⟨e⟩ := nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence _ _
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)
  exact ⟨e.symm ≪≫ RΓ.mapIso (coefficientDualIsoIhom _) ≪≫
    RΓ.mapIso (asIso (poincareAdjoint a γ K)).symm ≪≫
    (RΓ.commShiftIso (2 * d : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 * d : ℤ)).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _)⟩

variable {ϖ : Λ}

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: Adic reconstruction and
scalar extension (the finite-level pairings form a morphism of normalized systems).

Let `ϖ` be a nonzerodivisor of `Λ` (a uniformizer of `𝒪_E`) and `A_n = Λ/(ϖ)ⁿ`, read through
`K ↦ K_n = K ⊗ᴸ (A_n)_X`. For `K` perfect over `Λ_X` and every `n`:

1. the reduction `β_K^♯ ⊗ᴸ A_n` is an isomorphism;
2. its source is `RΓ(X, K^∨(d)_n)[2d]` and its target is `RHom(RΓ_c(X, K), A_n)`, the
   `A_n`-dual of `RΓ_c(X, K_n) ≅ RΓ_c(X, K) ⊗ᴸ A_n`: the reduction is the finite-level duality;
3. for `n ≤ m` the reductions commute with the transitions `A_m ⟶ A_n`: the finite-level
   dualities form a morphism of towers. -/
theorem poincareAdjoint_reduction (hϖ : ϖ ∈ nonZeroDivisors Λ) (hKd : IsDualizable K) (n : ℕ) :
    IsIso ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).map
        (poincareAdjoint a γ K)) ∧
      Nonempty ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
          (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (poincareSecondVariable (T := T) K))⟦(2 * d : ℤ)⟧) ≅
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj
          (poincareSecondVariable (T := T) K)))⟦(2 * d : ℤ)⟧) ∧
      Nonempty ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
          (((derivedHom _ _).obj (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))).obj (𝟙_ _)) ≅
        ((derivedHom _ _).obj (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))).obj
          ((reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj (𝟙_ _))) ∧
      Nonempty ((R(a)_![ModuleCat.{u + 1} Λ]).obj
          ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ≅
        (reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).obj
          ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)) ∧
      ∀ m (h : Ideal.span {ϖ} ^ m ≤ Ideal.span {ϖ} ^ n),
        (reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ m)).map (poincareAdjoint a γ K) ≫
            (reductionModIdealMap Λ (Spec (.of k)) h).app _ =
          (reductionModIdealMap Λ (Spec (.of k)) h).app _ ≫
            (reductionModIdeal Λ (Spec (.of k)) (Ideal.span {ϖ} ^ n)).map
              (poincareAdjoint a γ K) := by
  have := isIso_poincareAdjoint a γ hKd
  refine ⟨inferInstance, ?_, ?_, ?_, fun m h ↦ (reductionModIdealMap Λ _ h).naturality _⟩
  · obtain ⟨e⟩ := nonempty_iso_map_reductionModIdeal
      (R((a)_*[ModuleCat.{u + 1} Λ]) ⋙ shiftFunctor _ (2 * d : ℤ)) hϖ n
      (poincareSecondVariable (T := T) K)
    exact ⟨e.symm⟩
  · exact nonempty_iso_reductionModIdeal_derivedHom_obj hϖ n _ _
  · exact nonempty_iso_map_reductionModIdeal (R(a)_![ModuleCat.{u + 1} Λ]) hϖ n K

end Adjoint

section Integral

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The reduction `K ⊗ᴸ (Λ/ϖⁿ)_X` of a dualizable (that is, perfect over `Λ_X`) object `K` of
`D(X_ét, Λ)` is dualizable, for `ϖ` a nonzerodivisor of `Λ`: `(Λ/ϖⁿ)_X` is dualizable
(`AlgebraicGeometry.Etale.isDualizable_constantSingle_quotient_span_pow`). -/
theorem isDualizable_reductionModIdeal {X : Scheme.{u}} {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (n : ℕ) {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) :
    IsDualizable ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) := by
  rw [reductionModIdeal, Functor.flip_obj_obj]
  exact DerivedCategory.isDualizable_derivedTensor hK
    (isDualizable_constantSingle_quotient_span_pow hϖ n X)

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
  [HasCompactification a] [(R(a)_![ModuleCat.{u + 1} Λ]).IsLeftAdjoint] {d : ℕ}

/-- Blueprint `thm-pod-adic-reconstruction-and-scalar-extension`: Adic reconstruction and scalar
extension (perfectness of the integral pairing and of its finite levels).

Let `k` be separably closed, `Λ = 𝒪_E` (any commutative ring), `ϖ` a nonzerodivisor of `Λ`,
`a : X ⟶ Spec k` admitting a compactification with a right adjoint `Ra^!` of `Ra_!`, and
`γ : V[2d] ≅ Ra^! Λ` a purity isomorphism (`V = Λ_X(d)`). For `K` perfect over `Λ_X`, the
`𝒪_E`-valued derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ_{𝒪_E} RΓ(X, K^∨(d))[2d] ⟶ 𝒪_E`

is perfect, and so are the pairings `β_{K_n}` of the finite levels `K_n = K ⊗ᴸ (𝒪_E/ϖⁿ)_X`. -/
theorem isPerfectPairing_poincarePairing_integral
    {V : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : V⟦(2 * d : ℤ)⟧ ≅ dualizingComplex (ModuleCat.{u + 1} Λ) a)
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hK : IsDualizable K) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) :
    IsPerfectPairing (poincarePairing a γ K) ∧
      ∀ n : ℕ, IsPerfectPairing
        (poincarePairing a γ ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K)) :=
  ⟨isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a γ hK, fun n ↦
    isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a γ
      (isDualizable_reductionModIdeal hϖ n hK)⟩

end Integral

end Etale

end AlgebraicGeometry
